#!/usr/bin/env python3
"""rebuild_tool.py — 跨项目增量重建计划工具（纯 Python 标准库，单文件）。

功能：
  * 解析项目定义（名称 + 产出文件列表）、依赖定义、变更操作流
  * 跨项目传播：项目变更时，依赖它的项目连锁重建（增量，只重建受影响项目）
  * 错误报告：共享产物冲突 / 依赖缺失 / 依赖环 / 重建失败级联 / 同轮重复触发 / 操作引用未知项目
  * 重建历史写入 JSONL 文件，可追溯（--show-history 查看）

输入文件格式（# 开头为注释，空行忽略）：
  项目定义:  项目名: 产出1 产出2 ...
  依赖定义:  项目名: 依赖项目1 依赖项目2 ...
  变更操作:  项目名: 变更原因（每行一条，构成操作流）

用法示例：
  python3 rebuild_tool.py --projects examples/projects.txt \
      --deps examples/deps.txt --ops examples/ops.txt
  python3 rebuild_tool.py --projects examples/projects.txt \
      --deps examples/deps.txt --ops examples/ops2.txt --fail util
  python3 rebuild_tool.py --show-history 5
"""

import argparse
import json
import sys
import uuid
from collections import deque
from datetime import datetime, timezone, timedelta

DEFAULT_HISTORY = "rebuild_history.jsonl"


# ---------------------------------------------------------------- 输入解析

def iter_lines(path):
    """逐行产出 (行号, 去注释去空白后的内容)。"""
    with open(path, "r", encoding="utf-8") as fh:
        for lineno, raw in enumerate(fh, 1):
            line = raw.split("#", 1)[0].strip()
            if line:
                yield lineno, line


def split_def(line):
    """把 '名字: 其余内容' 拆成 (名字, 其余内容)，没有冒号时其余内容为空。"""
    if ":" in line:
        name, rest = line.split(":", 1)
    else:
        name, rest = line, ""
    return name.strip(), rest.strip()


def parse_projects(path, errors):
    """解析项目定义，返回 {项目名: [产出文件...]}（保持定义顺序）。"""
    projects = {}
    for lineno, line in iter_lines(path):
        name, rest = split_def(line)
        if not name:
            errors.append(("PARSE", f"项目定义 第{lineno}行：缺少项目名，已忽略"))
            continue
        if name in projects:
            errors.append(("DUP_PROJECT", f"项目 '{name}' 被重复定义（第{lineno}行），以首次定义为准"))
            continue
        projects[name] = rest.split()
    return projects


def parse_deps(path, projects, errors):
    """解析依赖定义，返回 {项目名: [依赖项目...]}，校验并剔除非法边。"""
    deps = {name: [] for name in projects}
    for lineno, line in iter_lines(path):
        name, rest = split_def(line)
        if name not in projects:
            errors.append(("UNKNOWN_PROJECT",
                           f"依赖定义 第{lineno}行：项目 '{name}' 未定义，该行已忽略"))
            continue
        for dep in rest.split():
            if dep not in projects:
                errors.append(("MISSING_DEP",
                               f"项目 '{name}' 依赖了未定义的项目 '{dep}'（第{lineno}行），该依赖边已忽略"))
                continue
            if dep not in deps[name]:
                deps[name].append(dep)
    return deps


def parse_ops(path, errors):
    """解析变更操作流，返回 [(项目名, 原因, 行号)]。"""
    ops = []
    for lineno, line in iter_lines(path):
        name, reason = split_def(line)
        ops.append((name, reason or "手动触发", lineno))
    return ops


# ---------------------------------------------------------------- 图算法

def find_cycles(deps):
    """Tarjan SCC（迭代实现），返回依赖环列表，每个环是排序后的项目名列表。"""
    index_of, lowlink, on_stack, stack = {}, {}, set(), []
    cycles = []
    counter = 0
    for root in deps:
        if root in index_of:
            continue
        index_of[root] = lowlink[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)
        work = [(root, iter(deps[root]))]
        while work:
            node, it = work[-1]
            descended = False
            for nxt in it:
                if nxt not in index_of:
                    index_of[nxt] = lowlink[nxt] = counter
                    counter += 1
                    stack.append(nxt)
                    on_stack.add(nxt)
                    work.append((nxt, iter(deps[nxt])))
                    descended = True
                    break
                if nxt in on_stack:
                    lowlink[node] = min(lowlink[node], index_of[nxt])
            if descended:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                lowlink[parent] = min(lowlink[parent], lowlink[node])
            if lowlink[node] == index_of[node]:
                scc = []
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    scc.append(member)
                    if member == node:
                        break
                if len(scc) > 1 or scc[0] in deps[scc[0]]:  # 多人环或自环
                    cycles.append(sorted(scc))
    return cycles


def topo_order(nodes, deps):
    """对 nodes 集合按依赖关系做 Kahn 拓扑排序（依赖在前），结果确定性。"""
    nodes = set(nodes)
    indegree = {n: 0 for n in nodes}
    dependents = {n: [] for n in nodes}
    for n in nodes:
        for d in deps[n]:
            if d in nodes:
                indegree[n] += 1
                dependents[d].append(n)
    ready = sorted(n for n in nodes if indegree[n] == 0)
    order = []
    while ready:
        node = ready.pop(0)
        order.append(node)
        for child in sorted(dependents[node]):
            indegree[child] -= 1
            if indegree[child] == 0:
                ready.append(child)
        ready.sort()
    return order


# ---------------------------------------------------------------- 核心规划

def build_plan(projects, deps, ops, fail_set, errors):
    """根据变更操作流计算重建计划，返回计划条目列表。"""
    # 1. 共享产物冲突
    artifact_owners = {}
    for name, outputs in projects.items():
        for art in outputs:
            artifact_owners.setdefault(art, []).append(name)
    for art in sorted(artifact_owners):
        owners = artifact_owners[art]
        if len(owners) > 1:
            errors.append(("CONFLICT",
                           f"产物文件 '{art}' 被多个项目共同产出: {', '.join(owners)}"))

    # 2. 依赖环
    cycle_members = set()
    for cyc in find_cycles(deps):
        cycle_members.update(cyc)
        errors.append(("CYCLE", f"检测到依赖环，环上项目: {' -> '.join(cyc)}"))

    # 3. 变更操作流：过滤未知项目、检测同轮重复触发
    trigger_reason = {}
    trigger_count = {}
    for name, reason, lineno in ops:
        if name not in projects:
            errors.append(("UNKNOWN_OP",
                           f"操作流 第{lineno}行：变更操作引用了不存在的项目 '{name}'"
                           f"（原因: {reason}），已忽略"))
            continue
        trigger_count[name] = trigger_count.get(name, 0) + 1
        trigger_reason.setdefault(name, reason)
    for name in sorted(trigger_count):
        if trigger_count[name] > 1:
            errors.append(("DUP_TRIGGER",
                           f"项目 '{name}' 在本轮被重复触发 {trigger_count[name]} 次，按一次变更处理"))

    # 4. 反向依赖图，BFS 求受影响集合（增量：只有受影响项目进入计划）
    dependents = {name: [] for name in projects}
    for name in projects:
        for d in deps[name]:
            dependents[d].append(name)
    affected = set()
    queue = deque(sorted(trigger_reason))
    while queue:
        node = queue.popleft()
        if node in affected:
            continue
        affected.add(node)
        queue.extend(sorted(dependents[node]))

    # 5. 拓扑排序 + 模拟重建；失败项目的下游级联跳过
    cyclic = affected & cycle_members
    for name in sorted(cyclic):
        errors.append(("CYCLE_SKIP", f"项目 '{name}' 位于依赖环上，无法确定构建顺序，重建失败"))
    order = topo_order(affected - cyclic, deps)

    failed = set()
    plan = []
    for name in sorted(cyclic):
        plan.append({"project": name, "status": "failed",
                     "reason": "位于依赖环上", "trigger": "propagated"})
    for name in order:
        bad_upstreams = sorted(d for d in deps[name]
                               if d in affected and (d in failed or d in cyclic))
        if bad_upstreams:
            failed.add(name)
            errors.append(("CASCADE",
                           f"项目 '{name}' 未重建：上游 {', '.join(bad_upstreams)} 重建失败（级联跳过）"))
            plan.append({"project": name, "status": "skipped",
                         "reason": f"上游 {', '.join(bad_upstreams)} 重建失败",
                         "trigger": "propagated"})
            continue
        if name in trigger_reason:
            reason, trigger = trigger_reason[name], "direct"
        else:
            ups = sorted(d for d in deps[name] if d in affected)
            reason, trigger = f"连锁重建：上游 {', '.join(ups)} 发生变更", "propagated"
        if name in fail_set:
            failed.add(name)
            errors.append(("BUILD_FAIL", f"项目 '{name}' 重建失败"))
            plan.append({"project": name, "status": "failed",
                         "reason": reason, "trigger": trigger})
        else:
            plan.append({"project": name, "status": "rebuilt",
                         "reason": reason, "trigger": trigger})
    return plan


# ---------------------------------------------------------------- 历史

def append_history(path, record):
    with open(path, "a", encoding="utf-8") as fh:
        fh.write(json.dumps(record, ensure_ascii=False) + "\n")


def show_history(path, count):
    try:
        with open(path, "r", encoding="utf-8") as fh:
            records = [json.loads(line) for line in fh if line.strip()]
    except FileNotFoundError:
        print(f"历史文件 '{path}' 不存在，尚无重建记录。")
        return 0
    for rec in records[-count:]:
        rebuilt = [p["project"] for p in rec["plan"] if p["status"] == "rebuilt"]
        print(f"[{rec['run_id']}] {rec['time']}  触发: "
              f"{', '.join(rec['triggers']) or '(无有效触发)'}")
        print(f"  重建 {len(rebuilt)} 项: {', '.join(rebuilt) or '(无)'}"
              f"  错误 {len(rec['errors'])} 条  结果: {'成功' if rec['ok'] else '有错误'}")
    return 0


# ---------------------------------------------------------------- 入口

def main(argv=None):
    ap = argparse.ArgumentParser(
        description="跨项目增量重建计划工具（纯标准库）",
        epilog=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--projects", help="项目定义文件：每行 '项目名: 产出文件...'")
    ap.add_argument("--deps", help="依赖定义文件：每行 '项目名: 依赖项目...'")
    ap.add_argument("--ops", help="变更操作流文件：每行 '项目名: 变更原因'")
    ap.add_argument("--fail", default="",
                    help="逗号分隔的项目名列表，模拟这些项目重建失败（用于验证级联失败）")
    ap.add_argument("--history", default=DEFAULT_HISTORY,
                    help=f"重建历史 JSONL 文件路径（默认 {DEFAULT_HISTORY}）")
    ap.add_argument("--show-history", type=int, metavar="N", nargs="?", const=10,
                    help="查看最近 N 条重建历史（默认 10 条）后退出")
    args = ap.parse_args(argv)

    if args.show_history is not None:
        return show_history(args.history, args.show_history)
    if not (args.projects and args.deps and args.ops):
        ap.error("必须同时提供 --projects、--deps 和 --ops（或使用 --show-history）")

    errors = []
    projects = parse_projects(args.projects, errors)
    deps = parse_deps(args.deps, projects, errors)
    ops = parse_ops(args.ops, errors)
    fail_set = {n.strip() for n in args.fail.split(",") if n.strip()}
    for name in sorted(fail_set - set(projects)):
        errors.append(("UNKNOWN_FAIL", f"--fail 指定的项目 '{name}' 不存在，已忽略"))

    plan = build_plan(projects, deps, ops, fail_set, errors)

    # 输出重建计划
    print("=" * 60)
    print("重建计划")
    print("=" * 60)
    if not plan:
        print("（无受影响项目，无需重建）")
    status_mark = {"rebuilt": "[重建]", "failed": "[失败]", "skipped": "[跳过]"}
    for i, item in enumerate(plan, 1):
        print(f"{i:>3}. {status_mark[item['status']]} {item['project']}"
              f"  （{item['reason']}）")

    # 输出错误清单
    print()
    print("=" * 60)
    print(f"错误报告（共 {len(errors)} 条）")
    print("=" * 60)
    if not errors:
        print("（无错误）")
    for code, msg in errors:
        print(f"[{code}] {msg}")

    # 写入历史
    now = datetime.now(timezone(timedelta(hours=8)))
    record = {
        "run_id": now.strftime("%Y%m%d-%H%M%S") + "-" + uuid.uuid4().hex[:6],
        "time": now.isoformat(timespec="seconds"),
        "triggers": sorted({name for name, _, _ in ops if name in projects}),
        "plan": plan,
        "errors": [{"code": c, "message": m} for c, m in errors],
        "ok": not errors,
    }
    append_history(args.history, record)
    print()
    print(f"本轮记录已写入历史文件: {args.history} (run_id={record['run_id']})")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
