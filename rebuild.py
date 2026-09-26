#!/usr/bin/env python3
"""rebuild.py — 跨项目增量重建计划工具（纯 Python 标准库，单文件）。

输入（JSON 文件）：
{
  "projects":     {"项目名": ["产物文件", ...], ...},
  "dependencies": {"项目名": ["依赖的项目", ...], ...},
  "operations":   [{"project": "项目名", "reason": "变更原因"}, ...],
  "failures":     ["本轮重建会失败的项目名", ...]        // 可选，模拟构建失败
}

用法：
  python3 rebuild.py run spec.json [--history FILE]   生成计划、执行（模拟）重建、记录历史
  python3 rebuild.py demo                             生成 demo_spec.json 并跑一遍全场景示例
  python3 rebuild.py history [--history FILE]         查看重建历史
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from heapq import heapify, heappop, heappush
from pathlib import Path

DEFAULT_HISTORY = "rebuild_history.jsonl"


class Reporter:
    def __init__(self):
        self.errors = []

    def add(self, kind, message):
        self.errors.append({"type": kind, "message": message})


def load_spec(path):
    with open(path, encoding="utf-8") as f:
        data = json.load(f)
    return (
        data.get("projects", {}),
        data.get("dependencies", {}),
        data.get("operations", []),
        set(data.get("failures", [])),
    )


def validate_static(projects, deps, rep):
    """产物冲突、缺失依赖、依赖环（静态检查，与操作流无关）。"""
    owner = {}
    for name, outputs in projects.items():
        for art in outputs:
            if art in owner and owner[art] != name:
                rep.add("ARTIFACT_CONFLICT",
                        f"产物 '{art}' 同时由项目 '{owner[art]}' 与 '{name}' 产出")
            else:
                owner[art] = name

    for name, ds in deps.items():
        if name not in projects:
            rep.add("UNKNOWN_PROJECT", f"依赖定义引用了不存在的项目 '{name}'")
        for d in ds:
            if d not in projects:
                rep.add("MISSING_DEPENDENCY", f"项目 '{name}' 依赖了不存在的项目 '{d}'")

    return find_cycles(set(projects), deps, rep)


def find_cycles(nodes, deps, rep):
    """Tarjan SCC，报告所有环上的项目，返回环上节点集合。"""
    sys.setrecursionlimit(max(10000, len(nodes) * 4))
    index, low, on_stack, stack = {}, {}, set(), []
    counter = [0]
    cyclic = set()

    def strongconnect(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on_stack.add(v)
        for w in deps.get(v, []):
            if w not in nodes:
                continue
            if w not in index:
                strongconnect(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            scc = []
            while True:
                w = stack.pop()
                on_stack.discard(w)
                scc.append(w)
                if w == v:
                    break
            if len(scc) > 1 or (len(scc) == 1 and scc[0] in deps.get(scc[0], [])):
                cyclic.update(scc)
                rep.add("DEPENDENCY_CYCLE",
                        "依赖环上的项目: " + " -> ".join(sorted(scc)))

    for v in sorted(nodes):
        if v not in index:
            strongconnect(v)
    return cyclic


def collect_triggers(operations, projects, rep):
    """解析操作流：未知项目报错，同轮重复触发报错并去重。返回 {项目: 原因}。"""
    triggers = {}
    for i, op in enumerate(operations, 1):
        name = op.get("project")
        reason = op.get("reason", "(未说明)")
        if not name or name not in projects:
            rep.add("UNKNOWN_PROJECT",
                    f"第 {i} 个操作引用了不存在的项目 '{name}'（原因：{reason}）")
            continue
        if name in triggers:
            rep.add("DUPLICATE_TRIGGER",
                    f"项目 '{name}' 在同一轮被重复触发（首次：'{triggers[name]}'；"
                    f"重复：'{reason}'），已按一次处理")
            continue
        triggers[name] = reason
    return triggers


def affected_closure(triggers, projects, deps):
    """沿反向依赖传播，返回 {项目: 重建原因}（增量：只含受影响项目）。"""
    dependents = {n: [] for n in projects}
    for name, ds in deps.items():
        if name not in projects:
            continue
        for d in ds:
            if d in projects:
                dependents[d].append(name)

    reasons = dict(triggers)
    queue = list(triggers)
    while queue:
        src = queue.pop(0)
        for nxt in dependents[src]:
            if nxt not in reasons:
                reasons[nxt] = f"连锁重建：上游 '{src}' 变更"
                queue.append(nxt)
    return reasons


def topo_order(nodes, deps):
    """对受影响子图做拓扑排序（依赖先建），按名字序保证输出稳定。"""
    indeg = {n: 0 for n in nodes}
    adj = {n: [] for n in nodes}
    for n in nodes:
        for d in deps.get(n, []):
            if d in nodes:
                indeg[n] += 1
                adj[d].append(n)
    heap = [n for n in nodes if indeg[n] == 0]
    heapify(heap)
    order = []
    while heap:
        n = heappop(heap)
        order.append(n)
        for m in adj[n]:
            indeg[m] -= 1
            if indeg[m] == 0:
                heappush(heap, m)
    return order


def run_round(spec_path, history_path):
    projects, deps, operations, failures = load_spec(spec_path)
    rep = Reporter()

    cyclic = validate_static(projects, deps, rep)
    triggers = collect_triggers(operations, projects, rep)
    affected = affected_closure(triggers, projects, deps)

    buildable = {n: r for n, r in affected.items() if n not in cyclic}
    for n in sorted(set(affected) & cyclic):
        rep.add("CYCLE_SKIP", f"项目 '{n}' 位于依赖环上，跳过重建")

    order = topo_order(set(buildable), deps)

    rebuilt, failed, skipped = [], [], []
    broken = set(cyclic)  # 环上节点视为不可用，下游级联跳过
    for name in order:
        bad_up = [d for d in deps.get(name, []) if d in broken]
        if bad_up:
            skipped.append(name)
            broken.add(name)
            rep.add("CASCADE_FAILURE",
                    f"项目 '{name}' 因上游 {sorted(bad_up)} 重建失败/不可用，跳过重建")
        elif name in failures:
            failed.append(name)
            broken.add(name)
            rep.add("BUILD_FAILED", f"项目 '{name}' 重建失败，其下游将不会重建")
        else:
            rebuilt.append(name)

    round_no = 1
    hpath = Path(history_path)
    if hpath.exists():
        round_no = sum(1 for _ in hpath.open(encoding="utf-8")) + 1

    record = {
        "round": round_no,
        "time": datetime.now(timezone.utc).isoformat(),
        "spec": str(spec_path),
        "operations": operations,
        "rebuilt": rebuilt,
        "failed": failed,
        "skipped": skipped,
        "errors": rep.errors,
    }
    with hpath.open("a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False) + "\n")

    print(f"== 重建计划（第 {round_no} 轮，拓扑序）==")
    if order:
        for i, name in enumerate(order, 1):
            mark = "成功" if name in rebuilt else ("失败" if name in failed else "跳过")
            print(f"  {i:>2}. {name:<12} [{mark}] {buildable[name]}")
    else:
        print("  （无受影响项目，无需重建）")

    print(f"\n== 错误清单（{len(rep.errors)} 条）==")
    if rep.errors:
        for e in rep.errors:
            print(f"  [{e['type']}] {e['message']}")
    else:
        print("  （无错误）")

    print(f"\n历史已追加到 {hpath}（第 {round_no} 轮）")
    return 1 if rep.errors else 0


def show_history(history_path):
    hpath = Path(history_path)
    if not hpath.exists():
        print(f"暂无历史记录（{hpath} 不存在）")
        return 0
    for line in hpath.read_text(encoding="utf-8").splitlines():
        r = json.loads(line)
        print(f"第 {r['round']} 轮 @ {r['time']}  spec={r['spec']}")
        print(f"  重建: {r['rebuilt'] or '无'}")
        print(f"  失败: {r['failed'] or '无'}  跳过: {r['skipped'] or '无'}")
        print(f"  错误: {len(r['errors'])} 条")
    return 0


DEMO_SPEC = {
    "projects": {
        "core": ["core.o"],
        "net": ["net.o"],
        "storage": ["storage.o"],
        "app": ["app.bin"],
        "ui": ["ui.bin", "theme.dat"],
        "plugin": ["plugin.so", "theme.dat"],
        "broken": ["broken.o"],
        "consumer": ["consumer.o"],
        "cycA": ["a.o"],
        "cycB": ["b.o"],
        "lonely": ["lonely.o"]
    },
    "dependencies": {
        "net": ["core"],
        "storage": ["core"],
        "app": ["net", "storage"],
        "ui": ["app", "nonexistent"],
        "plugin": ["app"],
        "broken": ["core"],
        "consumer": ["broken"],
        "cycA": ["cycB"],
        "cycB": ["cycA"],
        "ghost": ["core"]
    },
    "operations": [
        {"project": "core", "reason": "修复内存泄漏"},
        {"project": "core", "reason": "调整日志级别"},
        {"project": "cycA", "reason": "重构"},
        {"project": "nosuch", "reason": "误操作"}
    ],
    "failures": ["storage"]
}


def run_demo(history_path):
    spec_path = Path("demo_spec.json")
    spec_path.write_text(json.dumps(DEMO_SPEC, ensure_ascii=False, indent=2),
                         encoding="utf-8")
    print(f"已生成示例输入 {spec_path}，内容如下：\n")
    print(spec_path.read_text(encoding="utf-8"))
    print("-" * 60)
    return run_round(spec_path, history_path)


def main(argv=None):
    ap = argparse.ArgumentParser(description="跨项目增量重建计划工具")
    sub = ap.add_subparsers(dest="cmd")
    p_run = sub.add_parser("run", help="根据 spec 生成重建计划并记录历史")
    p_run.add_argument("spec")
    p_run.add_argument("--history", default=DEFAULT_HISTORY)
    p_demo = sub.add_parser("demo", help="运行内置全场景示例")
    p_demo.add_argument("--history", default=DEFAULT_HISTORY)
    p_his = sub.add_parser("history", help="查看重建历史")
    p_his.add_argument("--history", default=DEFAULT_HISTORY)
    args = ap.parse_args(argv)

    if args.cmd is None:
        ap.print_help()
        return 2
    if args.cmd == "run":
        return run_round(args.spec, args.history)
    if args.cmd == "demo":
        return run_demo(args.history)
    if args.cmd == "history":
        return show_history(args.history)
    return 2


if __name__ == "__main__":
    sys.exit(main())
