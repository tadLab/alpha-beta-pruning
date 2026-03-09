import { useState, useMemo, useEffect, useRef, useCallback } from "react";

const INF = 1e9;
const LEAF_GAP = 68;
const LVL_H = 110;
const NW = 44, NH = 28;
const PAD_X = 60, PAD_Y = 40;

function fv(v) {
  if (v === null || v === undefined) return "";
  if (v >= INF * 0.9) return "∞";
  if (v <= -INF * 0.9) return "-∞";
  return String(v);
}
function pv(s) {
  if (!s && s !== 0) return null;
  const t = String(s).trim();
  if (t === "inf" || t === "∞") return INF;
  if (t === "-inf" || t === "-∞") return -INF;
  const n = parseFloat(t);
  return isNaN(n) ? null : n;
}

let _id = 1;
function mkNode(depth = 0) { return { id: _id++, depth, children: [], leafInput: "", leafValue: null }; }
function cloneTree(n) { return { ...n, children: n.children.map(cloneTree) }; }
function setDepths(n, d = 0) { n.depth = d; n.children.forEach(c => setDepths(c, d + 1)); }
function addChild(root, pid) {
  const r = cloneTree(root);
  (function w(n) { if (n.id === pid) { n.children.push(mkNode(n.depth + 1)); return true; } return n.children.some(w); })(r);
  return r;
}
function removeNode(root, nid) {
  const r = cloneTree(root);
  (function w(n) { const i = n.children.findIndex(c => c.id === nid); if (i >= 0) { n.children.splice(i, 1); return true; } return n.children.some(w); })(r);
  return r;
}
function setLeaf(root, nid, val, raw) {
  const r = cloneTree(root);
  (function w(n) { if (n.id === nid) { n.leafInput = raw; n.leafValue = val; return true; } return n.children.some(w); })(r);
  return r;
}
function allNodes(root) { const out = []; (function w(n) { out.push(n); n.children.forEach(w); })(root); return out; }
function getNode(root, nid) { return allNodes(root).find(n => n.id === nid) || null; }
function allLeafsValid(root) {
  if (!root.children.length) return root.leafValue !== null;
  return root.children.every(allLeafsValid);
}

function computeLayout(root) {
  const pos = new Map(); let lx = 0;
  function assign(n) {
    if (!n.children.length) { pos.set(n.id, { x: PAD_X + lx++ * LEAF_GAP, y: PAD_Y + n.depth * LVL_H }); return; }
    n.children.forEach(assign);
    const xs = n.children.map(c => pos.get(c.id).x);
    pos.set(n.id, { x: (xs[0] + xs[xs.length - 1]) / 2, y: PAD_Y + n.depth * LVL_H });
  }
  assign(root);
  let W = 0, H = 0;
  for (const [, p] of pos) { W = Math.max(W, p.x); H = Math.max(H, p.y); }
  return { pos, svgW: W + PAD_X + 80, svgH: H + PAD_Y + 50 };
}

function recordSteps(root, rootIsMax) {
  const frames = [];
  const nodeVals = new Map(), nodeAlpha = new Map(), nodeBeta = new Map();
  const nodeStatus = new Map(), edgeStatus = new Map();
  allNodes(root).forEach(n => {
    nodeStatus.set(n.id, "unvisited"); nodeVals.set(n.id, null);
    n.children.forEach((_, i) => edgeStatus.set(`${n.id}:${i}`, "normal"));
  });
  function snap(desc, type) {
    frames.push({ desc, type, nodeVals: new Map(nodeVals), nodeAlpha: new Map(nodeAlpha), nodeBeta: new Map(nodeBeta), nodeStatus: new Map(nodeStatus), edgeStatus: new Map(edgeStatus) });
  }
  function pruneSub(n) { nodeStatus.set(n.id, "pruned"); n.children.forEach((c, i) => { edgeStatus.set(`${n.id}:${i}`, "pruned"); pruneSub(c); }); }
  function ab(n, a, b, isMax) {
    nodeStatus.set(n.id, "active"); nodeAlpha.set(n.id, a); nodeBeta.set(n.id, b);
    snap(`Vstupuji [${n.id}] (${isMax ? "MAX" : "MIN"})  α=${fv(a)}, β=${fv(b)}`, "enter");
    if (!n.children.length) {
      nodeVals.set(n.id, n.leafValue); nodeStatus.set(n.id, "done");
      snap(`List [${n.id}] = ${fv(n.leafValue)}`, "leaf"); return n.leafValue;
    }
    let best = isMax ? -INF : INF, bestIdx = -1;
    for (let i = 0; i < n.children.length; i++) {
      const c = n.children[i];
      if (nodeStatus.get(c.id) === "pruned") continue;
      const cv = ab(c, a, b, !isMax);
      if (isMax ? cv > best : cv < best) {
        if (bestIdx >= 0) edgeStatus.set(`${n.id}:${bestIdx}`, "old_best");
        best = cv; bestIdx = i; edgeStatus.set(`${n.id}:${i}`, "current_best");
        nodeVals.set(n.id, best);
        if (isMax && cv > a) a = cv;
        if (!isMax && cv < b) b = cv;
        nodeAlpha.set(n.id, a); nodeBeta.set(n.id, b);
        snap(`★ Nový nejlepší [${n.id}]: větev #${i + 1} → ${fv(best)}  (α=${fv(a)}, β=${fv(b)})`, "best");
      }
      if (a >= b) {
        for (let j = i + 1; j < n.children.length; j++) { edgeStatus.set(`${n.id}:${j}`, "pruned"); pruneSub(n.children[j]); }
        nodeAlpha.set(n.id, a); nodeBeta.set(n.id, b);
        snap(`✂ OŘEZ [${n.id}]  α=${fv(a)} ≥ β=${fv(b)} → přeskakuji ${n.children.length - i - 1} větví`, "prune");
        break;
      }
    }
    nodeStatus.set(n.id, "done"); nodeVals.set(n.id, best);
    snap(`Uzavírám [${n.id}] = ${fv(best)}`, "close"); return best;
  }
  snap("Počáteční stav", "init");
  ab(root, -INF, INF, rootIsMax);
  snap("Hotovo!", "done");
  return frames;
}

// ── BUILD SVG ─────────────────────────────────────────────────
function BuildTreeSVG({ root, layout, rootIsMax, selectedId, onSelectNode, onDoubleClickNode }) {
  const { pos, svgW, svgH } = layout;
  const edges = [], nodes = [];
  const isMax = d => rootIsMax ? d % 2 === 0 : d % 2 !== 0;

  function walk(n) {
    const p = pos.get(n.id); if (!p) return;
    n.children.forEach(c => {
      const cp = pos.get(c.id); if (!cp) return;
      edges.push(<line key={`e${n.id}-${c.id}`} x1={p.x} y1={p.y + 14} x2={cp.x} y2={cp.y - 14} stroke="#1a2d42" strokeWidth={1.5} />);
      walk(c);
    });

    const isLeaf = !n.children.length;
    const mx = isMax(n.depth);
    const hasVal = n.leafValue !== null;
    const selected = selectedId === n.id;

    nodes.push(
      <g key={`n${n.id}`} style={{ cursor: "pointer" }}
        onClick={e => { e.stopPropagation(); onSelectNode(n.id); }}
        onDoubleClick={e => { e.stopPropagation(); onDoubleClickNode(n.id); }}>
        {selected && (
          <rect x={p.x - NW / 2 - 5} y={p.y - NH / 2 - 5} width={NW + 10} height={NH + 10} rx={8}
            fill="#1d4ed825" stroke="#3b82f6" strokeWidth={2} />
        )}
        <rect x={p.x - NW / 2} y={p.y - NH / 2} width={NW} height={NH} rx={4}
          fill={selected ? "#0f2744" : isLeaf ? (hasVal ? "#0d2a0d" : "#1a0a0a") : "#070d1c"}
          stroke={selected ? "#3b82f6" : isLeaf ? (hasVal ? "#16a34a" : "#dc2626") : (mx ? "#ca8a04" : "#7c3aed")}
          strokeWidth={selected ? 2 : 1.5}
        />
        <text x={p.x} y={p.y + 5} textAnchor="middle"
          fill={selected ? "#93c5fd" : isLeaf ? (hasVal ? "#4ade80" : "#ef4444") : (mx ? "#fbbf24" : "#a78bfa")}
          fontSize={12} fontWeight="700" fontFamily="'JetBrains Mono',monospace"
          style={{ userSelect: "none" }}>
          {isLeaf ? (hasVal ? fv(n.leafValue) : "?") : (mx ? "MAX" : "MIN")}
        </text>
      </g>
    );
  }

  walk(root);

  return (
    <svg width={svgW} height={svgH}
      style={{ display: "block", minWidth: svgW, background: "#030712" }}
      onClick={() => onSelectNode(null)}>
      {edges}{nodes}
    </svg>
  );
}

// ── SOLVE SVG ─────────────────────────────────────────────────
const ECOL = { normal: "#1a2d42", current_best: "#3b82f6", old_best: "#f59e0b", pruned: "#2a0a0a" };

function SolveTreeSVG({ root, layout, frame, rootIsMax }) {
  const { pos, svgW, svgH } = layout;
  const edges = [], nodes = [];
  const isMax = d => rootIsMax ? d % 2 === 0 : d % 2 !== 0;

  function walk(n) {
    const p = pos.get(n.id); if (!p) return;
    n.children.forEach((c, i) => {
      const cp = pos.get(c.id); if (!cp) return;
      const es = frame.edgeStatus.get(`${n.id}:${i}`) || "normal";
      const mx = (p.x + cp.x) / 2, my = (p.y + 14 + cp.y - 14) / 2;
      edges.push(<line key={`e${n.id}${i}`} x1={p.x} y1={p.y + 14} x2={cp.x} y2={cp.y - 14}
        stroke={ECOL[es]} strokeWidth={es === "current_best" ? 3.5 : 1.5}
        strokeDasharray={es === "pruned" ? "4,3" : undefined} opacity={es === "pruned" ? 0.35 : 1} />);
      if (es === "old_best") edges.push(
        <line key={`ox1${n.id}${i}`} x1={mx - 8} y1={my - 6} x2={mx + 8} y2={my + 6} stroke="#f59e0b" strokeWidth={2.5} />,
        <line key={`ox2${n.id}${i}`} x1={mx + 8} y1={my - 6} x2={mx - 8} y2={my + 6} stroke="#f59e0b" strokeWidth={2.5} />);
      if (es === "pruned") edges.push(
        <line key={`px1${n.id}${i}`} x1={mx - 6} y1={my - 6} x2={mx + 6} y2={my + 6} stroke="#ef4444" strokeWidth={2} />,
        <line key={`px2${n.id}${i}`} x1={mx + 6} y1={my - 6} x2={mx - 6} y2={my + 6} stroke="#ef4444" strokeWidth={2} />);
      walk(c);
    });
    const st = frame.nodeStatus.get(n.id) || "unvisited";
    const val = frame.nodeVals.get(n.id);
    const alp = frame.nodeAlpha.get(n.id), bet = frame.nodeBeta.get(n.id);
    const active = st === "active", done = st === "done", pruned = st === "pruned";
    const mx = isMax(n.depth);
    nodes.push(<g key={`n${n.id}`} opacity={pruned ? 0.25 : 1}>
      <rect x={p.x - NW / 2} y={p.y - NH / 2} width={NW} height={NH} rx={4}
        fill={active ? "#13325e" : done ? "#091e3a" : "#05090f"}
        stroke={active ? "#60a5fa" : done ? "#1e3a5f" : "#0f1929"} strokeWidth={active ? 2.5 : 1.2} />
      <text x={p.x} y={p.y + 5} textAnchor="middle"
        fill={active ? "#93c5fd" : done ? "#e2e8f0" : "#1e3a5f"}
        fontSize={11} fontWeight="700" fontFamily="'JetBrains Mono',monospace">
        {val !== null ? fv(val) : ""}
      </text>
      {alp !== undefined && <>
        <text x={p.x + NW / 2 + 5} y={p.y - 2} textAnchor="start" fill="#4ade80" fontSize={6.5} fontFamily="monospace">α={fv(alp)}</text>
        <text x={p.x + NW / 2 + 5} y={p.y + 9} textAnchor="start" fill="#f87171" fontSize={6.5} fontFamily="monospace">β={fv(bet)}</text>
      </>}
      <text x={p.x - NW / 2 - 3} y={p.y + 5} textAnchor="end"
        fill={mx ? "#fbbf24" : "#a78bfa"} fontSize={6} fontFamily="monospace">
        {mx ? "MAX" : "MIN"}
      </text>
    </g>);
  }
  walk(root);
  return <svg width={svgW} height={svgH} style={{ display: "block", minWidth: svgW, background: "#030712" }}>{edges}{nodes}</svg>;
}

const TC = { init: "#334155", enter: "#38bdf8", leaf: "#64748b", best: "#fbbf24", prune: "#ef4444", close: "#4ade80", done: "#3b82f6" };

// ── INLINE VALUE INPUT (appears right on the node) ────────────
function InlineInput({ x, y, node, onSubmit, onCancel }) {
  const ref = useRef(null);
  const [val, setVal] = useState(node.leafInput || "");

  useEffect(() => { ref.current?.focus(); }, []);

  const submit = () => {
    const parsed = pv(val);
    if (parsed !== null) onSubmit(node.id, parsed, val);
    else onCancel();
  };

  return (
    <foreignObject x={x - 42} y={y + NH / 2 + 4} width={84} height={28}>
      <input
        ref={ref}
        value={val}
        onChange={e => setVal(e.target.value)}
        onKeyDown={e => {
          if (e.key === "Enter") submit();
          if (e.key === "Escape") onCancel();
        }}
        onBlur={submit}
        style={{
          width: "100%", boxSizing: "border-box",
          background: "#0a1628", border: "1px solid #3b82f6",
          color: "#38bdf8", fontFamily: "'JetBrains Mono',monospace",
          fontSize: 11, padding: "3px 6px", outline: "none",
          textAlign: "center",
        }}
        placeholder="num/inf"
      />
    </foreignObject>
  );
}

// ── QUICK BULK INPUT ──────────────────────────────────────────
function BulkInput({ leafCount, onSubmit, onCancel }) {
  const ref = useRef(null);
  const [val, setVal] = useState("");

  useEffect(() => { ref.current?.focus(); }, []);

  return (
    <div style={{
      position: "fixed", top: "50%", left: "50%", transform: "translate(-50%,-50%)",
      zIndex: 200, background: "#070d1c", border: "2px solid #3b82f6",
      padding: "20px 24px", minWidth: 340, boxShadow: "0 0 60px #000d",
      fontFamily: "'JetBrains Mono',monospace",
    }}>
      <div style={{ color: "#3b82f6", fontSize: 13, fontWeight: 700, marginBottom: 8 }}>
        Hromadné zadání hodnot listů
      </div>
      <div style={{ color: "#64748b", fontSize: 10, marginBottom: 12 }}>
        Zadej {leafCount} hodnot oddělených mezerou/čárkou (zleva doprava).
        <br />Použij <span style={{ color: "#38bdf8" }}>inf</span> / <span style={{ color: "#38bdf8" }}>-inf</span> pro ±∞
      </div>
      <input
        ref={ref}
        value={val}
        onChange={e => setVal(e.target.value)}
        onKeyDown={e => {
          if (e.key === "Enter") {
            const parts = val.split(/[\s,]+/).filter(Boolean);
            const parsed = parts.map(pv);
            if (parsed.length === leafCount && parsed.every(v => v !== null)) {
              onSubmit(parsed);
            }
          }
          if (e.key === "Escape") onCancel();
        }}
        placeholder={`např: 3 5 -2 inf 7 1 ${leafCount > 6 ? "..." : ""}`}
        style={{
          width: "100%", boxSizing: "border-box",
          background: "#060d1a", border: "1px solid #1e3a5f",
          color: "#38bdf8", fontFamily: "inherit", fontSize: 13,
          padding: "10px 14px", outline: "none",
        }}
      />
      <div style={{ display: "flex", gap: 8, marginTop: 10 }}>
        <button onClick={onCancel} style={{
          flex: 1, padding: "8px", border: "1px solid #1e293b",
          background: "transparent", color: "#64748b",
          fontFamily: "inherit", fontSize: 11, cursor: "pointer",
        }}>Esc · Zrušit</button>
        <button onClick={() => {
          const parts = val.split(/[\s,]+/).filter(Boolean);
          const parsed = parts.map(pv);
          if (parsed.length === leafCount && parsed.every(v => v !== null)) onSubmit(parsed);
        }} style={{
          flex: 1, padding: "8px", border: "none",
          background: "#1d4ed8", color: "#fff",
          fontFamily: "inherit", fontSize: 11, cursor: "pointer", fontWeight: 700,
        }}>Enter · Potvrdit</button>
      </div>
    </div>
  );
}

// ── PRESET TREES ──────────────────────────────────────────────
function buildUniform(branching, depth) {
  _id = 1;
  function build(d) {
    const n = mkNode(d);
    if (d < depth) for (let i = 0; i < branching; i++) n.children.push(build(d + 1));
    return n;
  }
  return build(0);
}

// ══════════════════════════════════════════════════════════════
//  APP
// ══════════════════════════════════════════════════════════════
export default function App() {
  const [mode, setMode]             = useState("build");
  const [rootIsMax, setRootIsMax]   = useState(true);
  const [tree, setTree]             = useState(() => mkNode(0));
  const [selectedId, setSelectedId] = useState(null);
  const [editingId, setEditingId]   = useState(null);
  const [frames, setFrames]         = useState(null);
  const [fi, setFi]                 = useState(0);
  const [playing, setPlaying]       = useState(false);
  const [speed, setSpeed]           = useState(650);
  const [showBulk, setShowBulk]     = useState(false);
  const timer = useRef(null);

  const layout = useMemo(() => computeLayout(tree), [tree]);
  const valid  = useMemo(() => allLeafsValid(tree), [tree]);
  const nodes  = useMemo(() => allNodes(tree), [tree]);
  const leafs  = nodes.filter(n => !n.children.length);
  const unset  = leafs.filter(n => n.leafValue === null).length;

  const selectedNode = useMemo(() => selectedId !== null ? getNode(tree, selectedId) : null, [tree, selectedId]);

  useEffect(() => {
    if (!playing || !frames) return;
    timer.current = setInterval(() =>
      setFi(i => { if (i >= frames.length - 1) { setPlaying(false); return i; } return i + 1; }), speed);
    return () => clearInterval(timer.current);
  }, [playing, speed, frames]);

  const startSolve = useCallback(() => {
    const r = cloneTree(tree); setDepths(r);
    setFrames(recordSteps(r, rootIsMax));
    setFi(0); setPlaying(false); setMode("solve"); setSelectedId(null); setEditingId(null);
  }, [tree, rootIsMax]);

  // ── Keyboard shortcuts ────────────────────────────────────
  useEffect(() => {
    if (mode !== "build") return;
    const handler = (e) => {
      if (e.target.tagName === "INPUT" || e.target.tagName === "TEXTAREA") return;
      if (showBulk) return;

      // A = add child to selected
      if (e.key === "a" || e.key === "A") {
        if (selectedId !== null) {
          e.preventDefault();
          setTree(t => addChild(t, selectedId));
        }
        return;
      }
      // D or Delete or Backspace = delete selected
      if (e.key === "d" || e.key === "D" || e.key === "Delete" || e.key === "Backspace") {
        if (selectedId !== null) {
          const node = getNode(tree, selectedId);
          if (node && node.depth > 0) {
            e.preventDefault();
            setTree(t => removeNode(t, selectedId));
            setSelectedId(null);
          }
        }
        return;
      }
      // V or Enter = set value on selected leaf
      if (e.key === "v" || e.key === "V" || e.key === "Enter") {
        if (selectedId !== null) {
          const node = getNode(tree, selectedId);
          if (node && !node.children.length) {
            e.preventDefault();
            setEditingId(selectedId);
          }
        }
        return;
      }
      // Escape = deselect
      if (e.key === "Escape") {
        setSelectedId(null);
        setEditingId(null);
        return;
      }
      // B = bulk input
      if (e.key === "b" || e.key === "B") {
        if (leafs.length > 0) {
          e.preventDefault();
          setShowBulk(true);
        }
        return;
      }
      // R = run algorithm
      if (e.key === "r" || e.key === "R") {
        if (valid) { e.preventDefault(); startSolve(); }
        return;
      }
    };
    window.addEventListener("keydown", handler);
    return () => window.removeEventListener("keydown", handler);
  }, [mode, selectedId, tree, showBulk, valid, leafs.length, startSolve]);

  // Solve mode keyboard
  useEffect(() => {
    if (mode !== "solve" || !frames) return;
    const handler = (e) => {
      if (e.key === "ArrowLeft" || e.key === "h") { setFi(i => Math.max(0, i - 1)); e.preventDefault(); }
      if (e.key === "ArrowRight" || e.key === "l") { setFi(i => Math.min(frames.length - 1, i + 1)); e.preventDefault(); }
      if (e.key === "Home") { setFi(0); e.preventDefault(); }
      if (e.key === "End") { setFi(frames.length - 1); e.preventDefault(); }
      if (e.key === " ") { setPlaying(p => !p); e.preventDefault(); }
      if (e.key === "Escape" || e.key === "e") { setMode("build"); e.preventDefault(); }
    };
    window.addEventListener("keydown", handler);
    return () => window.removeEventListener("keydown", handler);
  }, [mode, frames]);

  const frame  = frames?.[fi];
  const isLast = frames && fi === frames.length - 1;

  const rootVal = useMemo(() => {
    if (!frames) return null;
    return fv(frames[frames.length - 1].nodeVals.get(tree.id));
  }, [frames, tree]);

  const prunedCount = useMemo(() => {
    if (!frames) return 0;
    let c = 0;
    for (const [, s] of frames[frames.length - 1].nodeStatus) if (s === "pruned") c++;
    return c;
  }, [frames]);

  const handleDoubleClick = (id) => {
    const node = getNode(tree, id);
    if (!node) return;
    // Double-click on leaf → edit value; on internal → add child
    if (!node.children.length) {
      setSelectedId(id);
      setEditingId(id);
    } else {
      setTree(t => addChild(t, id));
    }
  };

  const handleBulkSubmit = (values) => {
    let t = cloneTree(tree);
    const allLeafs = [];
    (function w(n) { if (!n.children.length) allLeafs.push(n.id); else n.children.forEach(w); })(t);
    for (let i = 0; i < allLeafs.length && i < values.length; i++) {
      const raw = fv(values[i]);
      (function w(n) { if (n.id === allLeafs[i]) { n.leafValue = values[i]; n.leafInput = raw; return true; } return n.children.some(w); })(t);
    }
    setTree(t);
    setShowBulk(false);
  };

  const btnStyle = (active) => ({
    fontFamily: "inherit", fontSize: 11, cursor: "pointer",
    padding: "7px 14px", border: `1px solid ${active ? "#3b82f6" : "#1e293b"}`,
    background: active ? "#1e3a5f" : "transparent",
    color: active ? "#93c5fd" : "#64748b",
  });

  return (
    <div style={{ background: "#030712", minHeight: "100vh", padding: "18px 20px 48px", fontFamily: "'JetBrains Mono','Fira Code',monospace", color: "#e2e8f0" }}>
      <link href="https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;600;700&display=swap" rel="stylesheet" />

      {/* HEADER */}
      <div style={{ borderBottom: "1px solid #080f1e", paddingBottom: 14, marginBottom: 16, display: "flex", alignItems: "center", gap: 16, flexWrap: "wrap" }}>
        <div>
          <h1 style={{ margin: 0, fontSize: 17, color: "#3b82f6" }}>Minimax + α-β builder</h1>
          <p style={{ margin: "3px 0 0", fontSize: 9, color: "#1e3a5f" }}>FIT VUT · IZU</p>
        </div>
        <div style={{ marginLeft: "auto", display: "flex", gap: 8, alignItems: "center" }}>
          <div style={{ display: "flex", border: "1px solid #1e293b" }}>
            <button onClick={() => setMode("build")} style={btnStyle(mode === "build")}>Sestavit</button>
            <button onClick={() => valid && startSolve()}
              style={{ ...btnStyle(mode === "solve"), cursor: valid ? "pointer" : "not-allowed", color: mode === "solve" ? "#93c5fd" : valid ? "#64748b" : "#1e293b" }}>
              Řešit{unset > 0 ? ` (${unset}×?)` : ""}
            </button>
          </div>
          <select value={rootIsMax ? "max" : "min"} onChange={e => setRootIsMax(e.target.value === "max")}
            style={{ background: "#060d1a", color: "#94a3b8", border: "1px solid #1e3a5f", fontFamily: "inherit", fontSize: 11, padding: "6px 10px", outline: "none" }}>
            <option value="max">Kořen MAX</option>
            <option value="min">Kořen MIN</option>
          </select>
        </div>
      </div>

      {/* BUILD MODE */}
      {mode === "build" && (
        <>
          {/* Toolbar */}
          <div style={{ display: "flex", gap: 8, alignItems: "center", marginBottom: 12, flexWrap: "wrap" }}>
            <div style={{ display: "flex", gap: 16, padding: "8px 14px", background: "#070d1c", border: "1px solid #0f1929", fontSize: 11 }}>
              <span style={{ color: "#334155" }}>uzlů: <span style={{ color: "#94a3b8" }}>{nodes.length}</span></span>
              <span style={{ color: "#334155" }}>listů: <span style={{ color: "#94a3b8" }}>{leafs.length}</span></span>
              {unset > 0 ? <span style={{ color: "#dc2626" }}>{unset} nevyplněno</span> : <span style={{ color: "#16a34a" }}>vše vyplněno</span>}
            </div>

            {/* Preset trees */}
            <div style={{ display: "flex", gap: 4 }}>
              {[[2,2,"2×2"],[2,3,"2×3"],[3,2,"3×2"],[3,3,"3×3"]].map(([b,d,lbl]) => (
                <button key={lbl} onClick={() => { setTree(buildUniform(b, d)); setSelectedId(null); setEditingId(null); }}
                  style={{ fontFamily: "inherit", fontSize: 10, cursor: "pointer", padding: "6px 10px", border: "1px solid #1e293b", background: "transparent", color: "#64748b" }}>
                  {lbl}
                </button>
              ))}
            </div>

            <button onClick={() => leafs.length > 0 && setShowBulk(true)}
              style={{ fontFamily: "inherit", fontSize: 11, cursor: leafs.length > 0 ? "pointer" : "not-allowed", padding: "8px 14px", border: "1px solid #1e293b", background: "transparent", color: leafs.length > 0 ? "#38bdf8" : "#1e293b" }}>
              B · Hromadně
            </button>

            <button onClick={() => { _id = 1; setTree(mkNode(0)); setFrames(null); setSelectedId(null); setEditingId(null); }}
              style={{ fontFamily: "inherit", fontSize: 11, cursor: "pointer", padding: "8px 14px", border: "1px solid #3d1010", background: "transparent", color: "#ef4444" }}>
              Reset
            </button>

            <button onClick={startSolve} disabled={!valid}
              style={{ fontFamily: "inherit", fontSize: 12, cursor: valid ? "pointer" : "not-allowed", padding: "8px 22px", border: "none", background: valid ? "#1d4ed8" : "#0a1020", color: valid ? "#fff" : "#1e3a5f", letterSpacing: "0.5px", marginLeft: "auto" }}>
              R · Spustit
            </button>
          </div>

          {/* Shortcuts help */}
          <div style={{ padding: "6px 14px", background: "#050c18", border: "1px solid #0a1929", marginBottom: 14, fontSize: 10, color: "#334155", display: "flex", gap: 16, flexWrap: "wrap" }}>
            <span><kbd style={kbdStyle}>click</kbd> vyber · <kbd style={kbdStyle}>dblclick</kbd> přidej/edituj</span>
            <span><kbd style={kbdStyle}>A</kbd> přidej dítě · <kbd style={kbdStyle}>D</kbd> smaž · <kbd style={kbdStyle}>V</kbd> hodnota</span>
            <span><kbd style={kbdStyle}>B</kbd> hromadně · <kbd style={kbdStyle}>R</kbd> spusť</span>
          </div>

          <div style={{ overflow: "auto", border: "1px solid #080f1e", background: "#030712", maxHeight: 680, position: "relative" }}>
            <BuildTreeSVG
              root={tree} layout={layout} rootIsMax={rootIsMax}
              selectedId={selectedId} onSelectNode={id => { setSelectedId(prev => prev === id ? null : id); setEditingId(null); }}
              onDoubleClickNode={handleDoubleClick}
            />
            {/* Inline editor overlay */}
            {editingId !== null && (() => {
              const node = getNode(tree, editingId);
              const p = layout.pos.get(editingId);
              if (!node || !p || node.children.length) return null;
              return (
                <svg style={{ position: "absolute", top: 0, left: 0, width: layout.svgW, height: layout.svgH, pointerEvents: "none" }}>
                  <foreignObject x={p.x - 42} y={p.y + NH / 2 + 4} width={84} height={28} style={{ pointerEvents: "auto" }}>
                    <InlineValueInput
                      node={node}
                      onSubmit={(id, val, raw) => { setTree(t => setLeaf(t, id, val, raw)); setEditingId(null); }}
                      onCancel={() => setEditingId(null)}
                    />
                  </foreignObject>
                </svg>
              );
            })()}
          </div>

          {/* Node panel (still available for complex actions) */}
          {selectedNode && !editingId && (
            <div style={{
              position: "fixed", bottom: 24, right: 24, zIndex: 100,
              background: "#070d1c", border: "2px solid #1e3a5f",
              padding: "14px 18px", minWidth: 200,
              boxShadow: "0 0 40px #000a",
              fontFamily: "'JetBrains Mono',monospace",
            }}>
              <div style={{ display: "flex", justifyContent: "space-between", alignItems: "center", marginBottom: 10 }}>
                <span style={{ color: (rootIsMax ? selectedNode.depth % 2 === 0 : selectedNode.depth % 2 !== 0) ? "#fbbf24" : "#a78bfa", fontSize: 10, fontWeight: 700 }}>
                  {(rootIsMax ? selectedNode.depth % 2 === 0 : selectedNode.depth % 2 !== 0) ? "MAX" : "MIN"}
                  <span style={{ color: "#1e3a5f" }}> · #{selectedNode.id}</span>
                </span>
                <button onClick={() => setSelectedId(null)} style={{ background: "none", border: "none", color: "#334155", cursor: "pointer", fontSize: 16, padding: "0 4px" }}>×</button>
              </div>

              <div style={{ display: "flex", gap: 6, flexWrap: "wrap" }}>
                <button onClick={() => { setTree(t => addChild(t, selectedId)); }}
                  style={{ flex: 1, padding: "8px", border: "1px solid #2563eb", background: "#0d2244", color: "#60a5fa", fontFamily: "inherit", fontSize: 11, cursor: "pointer", fontWeight: 700 }}>
                  A · Dítě
                </button>
                {!selectedNode.children.length && (
                  <button onClick={() => setEditingId(selectedId)}
                    style={{ flex: 1, padding: "8px", border: "1px solid #0e7490", background: "#0a1e2e", color: "#38bdf8", fontFamily: "inherit", fontSize: 11, cursor: "pointer", fontWeight: 700 }}>
                    V · Hodnota
                  </button>
                )}
                {selectedNode.depth > 0 && (
                  <button onClick={() => { setTree(t => removeNode(t, selectedId)); setSelectedId(null); }}
                    style={{ flex: 1, padding: "8px", border: "1px solid #7f1d1d", background: "#200808", color: "#ef4444", fontFamily: "inherit", fontSize: 11, cursor: "pointer" }}>
                    D · Smazat
                  </button>
                )}
              </div>
            </div>
          )}

          {/* Bulk input modal */}
          {showBulk && (
            <BulkInput
              leafCount={leafs.length}
              onSubmit={handleBulkSubmit}
              onCancel={() => setShowBulk(false)}
            />
          )}
        </>
      )}

      {/* SOLVE MODE */}
      {mode === "solve" && frames && frame && (
        <>
          <div style={{ display: "flex", gap: 16, padding: "8px 14px", background: "#070d1c", border: "1px solid #0f1929", marginBottom: 12, fontSize: 11, flexWrap: "wrap", alignItems: "center" }}>
            <span style={{ color: "#334155" }}>krok: <span style={{ color: "#38bdf8" }}>{fi + 1}/{frames.length}</span></span>
            <span style={{ color: "#334155" }}>ořezáno: <span style={{ color: "#ef4444" }}>{prunedCount}</span></span>
            <div style={{ flexGrow: 1 }} />
            <span style={{ color: "#3b82f6" }}>━ nejlepší</span>
            <span style={{ color: "#f59e0b" }}>✕ překonán</span>
            <span style={{ color: "#ef4444" }}>✕ ořez</span>
            <span style={{ color: "#4ade80" }}>α</span>
            <span style={{ color: "#f87171" }}>β</span>
          </div>

          <div style={{ display: "flex", gap: 8, alignItems: "center", flexWrap: "wrap", marginBottom: 10 }}>
            {[["⏮", () => setFi(0), fi === 0], ["◀", () => setFi(i => Math.max(0, i - 1)), fi === 0],
              ["▶", () => setFi(i => Math.min(frames.length - 1, i + 1)), isLast], ["⏭", () => setFi(frames.length - 1), isLast]
            ].map(([lbl, fn, dis], i) => (
              <button key={i} onClick={fn} disabled={dis} style={{ fontFamily: "inherit", fontSize: 12, cursor: dis ? "not-allowed" : "pointer", padding: "7px 12px", border: "1px solid #1e293b", background: "transparent", color: dis ? "#1e293b" : "#64748b" }}>{lbl}</button>
            ))}
            <button onClick={() => setPlaying(p => !p)} style={{ fontFamily: "inherit", fontSize: 12, cursor: "pointer", padding: "8px 22px", border: "none", background: playing ? "#78350f" : "#1d4ed8", color: "#fff", letterSpacing: "0.5px" }}>
              {playing ? "⏸ Pauza" : "Space · Play"}
            </button>

            <span style={{ color: "#334155", fontSize: 10, marginLeft: 8 }}>
              <kbd style={kbdStyle}>←→</kbd> krok · <kbd style={kbdStyle}>Space</kbd> play · <kbd style={kbdStyle}>Esc</kbd> zpět
            </span>

            <div style={{ marginLeft: "auto", display: "flex", gap: 8, alignItems: "center" }}>
              <span style={{ color: "#1e3a5f", fontSize: 9 }}>RYCHLOST</span>
              <input type="range" min={80} max={1800} step={80} value={1880 - speed}
                onChange={e => setSpeed(1880 - parseInt(e.target.value))} style={{ width: 70, accentColor: "#3b82f6" }} />
            </div>
          </div>

          <div style={{ background: "#080f1e", height: 4, marginBottom: 10, cursor: "pointer", borderRadius: 2 }}
            onClick={e => { const r = e.currentTarget.getBoundingClientRect(); setFi(Math.round(((e.clientX - r.left) / r.width) * (frames.length - 1))); }}>
            <div style={{ background: "linear-gradient(90deg,#1d4ed8,#3b82f6)", height: "100%", borderRadius: 2, width: `${(fi / Math.max(1, frames.length - 1)) * 100}%`, transition: "width 0.07s" }} />
          </div>

          <div style={{ background: "#070d1c", borderLeft: `3px solid ${TC[frame.type] || "#1e3a5f"}`, padding: "9px 16px", marginBottom: 12, fontSize: 12, display: "flex", gap: 12, alignItems: "center" }}>
            <span style={{ color: "#1e3a5f", fontSize: 9, minWidth: 50 }}>krok {fi + 1}</span>
            <span style={{ color: TC[frame.type] || "#94a3b8" }}>{frame.desc}</span>
          </div>

          <div style={{ overflow: "auto", border: "1px solid #080f1e", background: "#030712", maxHeight: 640 }}>
            <SolveTreeSVG root={tree} layout={layout} frame={frame} rootIsMax={rootIsMax} />
          </div>

          {isLast && (
            <div style={{ marginTop: 14, display: "inline-flex", gap: 32, padding: "14px 24px", background: "#050d1e", border: "1px solid #1e3a5f", flexWrap: "wrap", alignItems: "flex-end" }}>
              <div>
                <div style={{ color: "#1e3a5f", fontSize: 9, letterSpacing: "1px", marginBottom: 4 }}>HODNOTA KOŘENE</div>
                <span style={{ color: "#3b82f6", fontSize: 28, fontWeight: 700 }}>{rootVal}</span>
              </div>
              <div>
                <div style={{ color: "#1e3a5f", fontSize: 9, letterSpacing: "1px", marginBottom: 4 }}>OŘEZÁNO</div>
                <span style={{ color: "#ef4444", fontSize: 22 }}>{prunedCount}</span>
              </div>
              <div>
                <div style={{ color: "#1e3a5f", fontSize: 9, letterSpacing: "1px", marginBottom: 4 }}>UZLŮ CELKEM</div>
                <span style={{ color: "#94a3b8", fontSize: 22 }}>{nodes.length}</span>
              </div>
              <button onClick={() => setMode("build")} style={{ fontFamily: "inherit", fontSize: 11, cursor: "pointer", padding: "8px 16px", border: "1px solid #1e3a5f", background: "transparent", color: "#64748b" }}>
                Esc · Zpět do editoru
              </button>
            </div>
          )}
        </>
      )}
    </div>
  );
}

// ── Small inline input component (no foreignObject wrapper) ──
function InlineValueInput({ node, onSubmit, onCancel }) {
  const ref = useRef(null);
  const [val, setVal] = useState(node.leafInput || "");
  useEffect(() => { ref.current?.focus(); }, []);
  return (
    <input
      ref={ref}
      value={val}
      onChange={e => setVal(e.target.value)}
      onKeyDown={e => {
        if (e.key === "Enter") {
          const parsed = pv(val);
          if (parsed !== null) onSubmit(node.id, parsed, val);
          else onCancel();
        }
        if (e.key === "Escape") onCancel();
        e.stopPropagation();
      }}
      onBlur={() => {
        const parsed = pv(val);
        if (parsed !== null) onSubmit(node.id, parsed, val);
        else onCancel();
      }}
      placeholder="num/inf"
      style={{
        width: "100%", boxSizing: "border-box",
        background: "#0a1628", border: "1px solid #3b82f6",
        color: "#38bdf8", fontFamily: "'JetBrains Mono',monospace",
        fontSize: 11, padding: "3px 6px", outline: "none",
        textAlign: "center",
      }}
    />
  );
}

const kbdStyle = {
  display: "inline-block", padding: "1px 5px",
  background: "#0f1929", border: "1px solid #1e293b",
  borderRadius: 3, color: "#60a5fa", fontSize: 9,
  fontFamily: "'JetBrains Mono',monospace",
};
