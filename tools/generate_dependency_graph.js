const fs = require("fs");
const path = require("path");

const root = path.resolve(__dirname, "..");
const outFile = path.join(root, "docs", "geocoq_dependency_graph.html");

function walk(dir) {
  const out = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      if (entry.name !== "_build" && entry.name !== ".git") out.push(...walk(full));
    } else if (entry.isFile() && entry.name.endsWith(".v")) {
      out.push(full);
    }
  }
  return out;
}

function stripComments(text) {
  let out = "";
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (text[i] === "(" && text[i + 1] === "*") {
      depth++;
      i++;
      continue;
    }
    if (depth && text[i] === "*" && text[i + 1] === ")") {
      depth--;
      i++;
      continue;
    }
    if (!depth) out += text[i];
  }
  return out;
}

function moduleName(file) {
  const rel = path.relative(root, file).replaceAll(path.sep, "/");
  if (rel.startsWith("theories/")) {
    return "GeoCoq." + rel.slice("theories/".length, -2).replaceAll("/", ".");
  }
  return rel.slice(0, -2).replaceAll("/", ".");
}

function shortName(id) {
  return id.split(".").at(-1);
}

function groupName(id) {
  const p = id.split(".");
  if (p[0] !== "GeoCoq") return "Other";
  if (p[1] === "Main" && p[2]) return `Main/${p[2]}`;
  if (p[1] === "Algebraic" && p[2] === "Counter_models" && p[3]) return `Algebraic/${p[3]}`;
  return p[1] || "Other";
}

function parseImports(text) {
  const imports = [];
  for (const line of stripComments(text).split(/\r?\n/)) {
    const match = line.match(/^\s*Require\s+(?:Import|Export)\s+(.+?)\.\s*$/);
    if (!match) continue;
    for (const token of match[1].trim().split(/\s+/)) {
      if (token.startsWith("GeoCoq.")) imports.push(token.replace(/;$/, ""));
    }
  }
  return imports;
}

const files = walk(root).sort();
const known = new Map(files.map((file) => [moduleName(file), file]));
const nodes = files.map((file) => {
  const id = moduleName(file);
  const rel = path.relative(root, file).replaceAll(path.sep, "/");
  return { id, label: shortName(id), path: rel, group: groupName(id), imports: [] };
});
const byId = new Map(nodes.map((node) => [node.id, node]));
const edges = [];

for (const node of nodes) {
  const text = fs.readFileSync(path.join(root, node.path), "utf8");
  node.imports = parseImports(text).filter((id) => known.has(id));
  for (const target of node.imports) edges.push({ source: node.id, target });
}

for (const node of nodes) {
  node.inDegree = edges.filter((edge) => edge.target === node.id).length;
  node.outDegree = edges.filter((edge) => edge.source === node.id).length;
}

const groups = [...new Set(nodes.map((node) => node.group))].sort();
const groupCounts = Object.fromEntries(groups.map((group) => [group, nodes.filter((node) => node.group === group).length]));
const groupEdges = new Map();
for (const edge of edges) {
  const a = byId.get(edge.source).group;
  const b = byId.get(edge.target).group;
  const key = `${a}|||${b}`;
  groupEdges.set(key, (groupEdges.get(key) || 0) + 1);
}

const data = {
  generatedAt: new Date().toISOString(),
  nodes,
  edges,
  groups,
  groupCounts,
  groupEdges: [...groupEdges.entries()].map(([key, count]) => {
    const [source, target] = key.split("|||");
    return { source, target, count };
  }),
};

const html = `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>GeoCoq Dependency Explorer</title>
<style>
:root {
  color-scheme: dark;
  --bg: #0b0f14;
  --panel: #101720;
  --panel2: #141e2a;
  --text: #eef4ff;
  --muted: #9aa9bd;
  --line: rgba(148, 163, 184, .22);
  --blue: #60a5fa;
  --gold: #f4c95d;
  --green: #70d6a3;
}
* { box-sizing: border-box; }
body {
  margin: 0;
  height: 100vh;
  overflow: hidden;
  background: var(--bg);
  color: var(--text);
  font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
}
button, input, select {
  border: 1px solid rgba(255,255,255,.1);
  border-radius: 8px;
  background: rgba(255,255,255,.055);
  color: var(--text);
  font: inherit;
}
button { cursor: pointer; }
button:hover { border-color: rgba(96,165,250,.75); background: rgba(96,165,250,.12); }
.app { display: grid; grid-template-columns: 350px minmax(0, 1fr) 360px; height: 100vh; }
.side, .info {
  overflow: auto;
  background: linear-gradient(180deg, rgba(16,23,32,.98), rgba(12,18,27,.98));
  border-right: 1px solid rgba(255,255,255,.08);
}
.info { border-right: 0; border-left: 1px solid rgba(255,255,255,.08); }
.pad { padding: 18px; }
h1 { margin: 0 0 6px; font-size: 25px; line-height: 1.1; letter-spacing: 0; }
h2 { margin: 20px 0 10px; font-size: 12px; color: var(--muted); text-transform: uppercase; letter-spacing: .08em; }
p { margin: 0; color: var(--muted); line-height: 1.45; }
.stats { display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin: 16px 0; }
.stat { padding: 12px; border-radius: 8px; background: rgba(255,255,255,.045); border: 1px solid rgba(255,255,255,.07); }
.stat b { display: block; font-size: 24px; }
.stat span { color: var(--muted); font-size: 12px; }
.search { display: grid; gap: 9px; margin-top: 14px; }
.search input, .search select { width: 100%; padding: 10px 11px; }
.mode { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; margin-top: 10px; }
.mode button.active { background: rgba(96,165,250,.22); border-color: rgba(96,165,250,.8); }
.list { display: grid; gap: 6px; }
.item {
  display: grid;
  grid-template-columns: 10px minmax(0, 1fr) auto;
  gap: 8px;
  align-items: center;
  width: 100%;
  padding: 8px;
  text-align: left;
  color: var(--muted);
}
.item strong { color: var(--text); font-weight: 650; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.item small { display: block; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.swatch { width: 10px; height: 10px; border-radius: 50%; }
.badge { color: var(--text); font-variant-numeric: tabular-nums; font-size: 12px; }
.canvas-wrap { position: relative; overflow: hidden; }
.topbar {
  position: absolute;
  z-index: 4;
  top: 14px;
  left: 14px;
  right: 14px;
  display: flex;
  gap: 8px;
  align-items: center;
  pointer-events: none;
}
.topbar > * { pointer-events: auto; }
.topbar .hint {
  margin-left: auto;
  padding: 8px 10px;
  border: 1px solid rgba(255,255,255,.08);
  border-radius: 8px;
  background: rgba(10,15,22,.72);
  color: var(--muted);
  font-size: 13px;
}
.icon-btn { width: 42px; height: 38px; display: grid; place-items: center; font-size: 18px; }
svg { width: 100%; height: 100%; display: block; background:
  radial-gradient(circle at 70% 8%, rgba(96,165,250,.10), transparent 22rem),
  radial-gradient(circle at 20% 85%, rgba(112,214,163,.08), transparent 20rem),
  #0b0f14;
}
.edge { stroke: var(--line); stroke-width: 1.2; vector-effect: non-scaling-stroke; }
.edge.strong { stroke: rgba(244,201,93,.72); stroke-width: 2.4; }
.edge.reverse { stroke: rgba(96,165,250,.68); stroke-width: 2.4; }
.edge.cluster { stroke: rgba(96,165,250,.36); stroke-width: 2.2; stroke-dasharray: 5 7; }
.node { cursor: pointer; stroke: rgba(255,255,255,.82); stroke-width: 1.2; vector-effect: non-scaling-stroke; }
.node:hover { stroke-width: 3; }
.node.selected { stroke: white; stroke-width: 4; }
.node.cluster { fill-opacity: .72; stroke-width: 2; }
.node.faded, .edge.faded, .label.faded { opacity: .16; }
.label {
  fill: rgba(238,244,255,.92);
  font-size: 13px;
  font-weight: 650;
  text-anchor: middle;
  paint-order: stroke;
  stroke: rgba(11,15,20,.92);
  stroke-width: 4px;
  pointer-events: none;
}
.label.big { font-size: 16px; font-weight: 800; }
.sub-label {
  fill: rgba(154,169,189,.95);
  font-size: 10px;
  text-anchor: middle;
  paint-order: stroke;
  stroke: rgba(11,15,20,.92);
  stroke-width: 3px;
  pointer-events: none;
}
.tooltip {
  position: fixed;
  z-index: 20;
  display: none;
  max-width: 380px;
  padding: 10px 12px;
  border-radius: 8px;
  border: 1px solid rgba(255,255,255,.12);
  background: rgba(13,19,28,.96);
  box-shadow: 0 18px 55px rgba(0,0,0,.4);
  pointer-events: none;
}
.tooltip b { display: block; margin-bottom: 4px; }
code { color: #b7f7d8; word-break: break-word; }
.detail-title { margin: 0 0 8px; font-size: 21px; font-weight: 750; }
.pills { display: flex; flex-wrap: wrap; gap: 7px; margin: 13px 0; }
.pill { padding: 5px 8px; border-radius: 999px; background: rgba(255,255,255,.06); border: 1px solid rgba(255,255,255,.08); font-size: 12px; color: var(--text); }
.dep-button {
  width: 100%;
  padding: 8px;
  text-align: left;
  color: var(--muted);
  overflow: hidden;
  text-overflow: ellipsis;
}
.empty { color: var(--muted); font-size: 13px; }
@media (max-width: 1120px) {
  .app { grid-template-columns: 320px minmax(0, 1fr); }
  .info { display: none; }
}
</style>
</head>
<body>
<div class="app">
  <aside class="side">
    <div class="pad">
      <h1>GeoCoq Dependency Explorer</h1>
      <p>Start with the clean area map. Search or click a module to see its direct imports and reverse dependents.</p>
      <div class="stats">
        <div class="stat"><b>${nodes.length}</b><span>Coq files</span></div>
        <div class="stat"><b>${edges.length}</b><span>internal imports</span></div>
        <div class="stat"><b>${groups.length}</b><span>areas</span></div>
        <div class="stat"><b id="visibleCount">${groups.length}</b><span>shown</span></div>
      </div>
      <div class="search">
        <input id="search" placeholder="Search module or file">
        <select id="groupFilter"></select>
        <div class="mode">
          <button id="overviewBtn" class="active">Overview</button>
          <button id="modulesBtn">Modules</button>
        </div>
      </div>
      <h2>Results</h2>
      <div id="results" class="list"></div>
      <h2>Areas</h2>
      <div id="areas" class="list"></div>
    </div>
  </aside>
  <main class="canvas-wrap">
    <div class="topbar">
      <button id="zoomIn" class="icon-btn" title="Zoom in">+</button>
      <button id="zoomOut" class="icon-btn" title="Zoom out">-</button>
      <button id="resetView" class="icon-btn" title="Reset view">R</button>
      <button id="focusView" class="icon-btn" title="Focus selected">F</button>
      <div class="hint" id="hint">Drag to pan. Wheel or buttons to zoom. Hover nodes for details.</div>
    </div>
    <svg id="graph" aria-label="GeoCoq dependency graph"></svg>
    <div id="tooltip" class="tooltip"></div>
  </main>
  <section class="info">
    <div class="pad" id="details">
      <div class="detail-title">Clean Overview</div>
      <p>Each node is a GeoCoq area. Edge thickness means more imports between areas.</p>
    </div>
  </section>
</div>
<script>
const DATA = ${JSON.stringify(data)};
const colors = {
  "Axioms": "#f4c95d",
  "Coinc": "#67e8f9",
  "Main/Tarski_dev": "#70d6a3",
  "Main/Annexes": "#f0abfc",
  "Main/Highschool": "#c4b5fd",
  "Main/Meta_theory": "#fb923c",
  "Elements": "#93c5fd",
  "Algebraic": "#fb7185",
  "Algebraic/nD": "#f43f5e",
  "Algebraic/Planar": "#fda4af",
  "Other": "#94a3b8"
};
const svg = document.querySelector("#graph");
const tip = document.querySelector("#tooltip");
const details = document.querySelector("#details");
const search = document.querySelector("#search");
const groupFilter = document.querySelector("#groupFilter");
const visibleCount = document.querySelector("#visibleCount");
const nodes = DATA.nodes;
const edges = DATA.edges;
const byId = new Map(nodes.map(n => [n.id, n]));
const outgoing = new Map(nodes.map(n => [n.id, []]));
const incoming = new Map(nodes.map(n => [n.id, []]));
for (const e of edges) {
  outgoing.get(e.source).push(e.target);
  incoming.get(e.target).push(e.source);
}
let mode = "overview";
let selected = null;
let view = { x: 0, y: 0, w: 1200, h: 760 };
let pan = null;
let currentGraph = { nodes: [], edges: [] };

groupFilter.innerHTML = '<option value="all">All areas</option>' + DATA.groups.map(g => '<option value="' + esc(g) + '">' + esc(g) + '</option>').join("");
document.querySelector("#areas").innerHTML = DATA.groups.map(g => itemHtml(g, g, DATA.groupCounts[g], g)).join("");
document.querySelectorAll("#areas .item").forEach(btn => btn.addEventListener("click", () => {
  groupFilter.value = btn.dataset.id;
  mode = "modules";
  selected = null;
  syncButtons();
  render();
}));

function color(g) { return colors[g] || "#94a3b8"; }
function esc(s) { return String(s).replace(/[&<>"']/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c])); }
function label(id) { return id.split(".").at(-1); }
function itemHtml(id, title, subtitle, group) {
  return '<button class="item" data-id="' + esc(id) + '"><span class="swatch" style="background:' + color(group) + '"></span><span><strong>' + esc(title) + '</strong><small>' + esc(subtitle) + '</small></span><span class="badge"></span></button>';
}

function setMode(next) {
  mode = next;
  selected = null;
  syncButtons();
  render();
}

function syncButtons() {
  document.querySelector("#overviewBtn").classList.toggle("active", mode === "overview");
  document.querySelector("#modulesBtn").classList.toggle("active", mode === "modules");
}

document.querySelector("#overviewBtn").addEventListener("click", () => setMode("overview"));
document.querySelector("#modulesBtn").addEventListener("click", () => setMode("modules"));
search.addEventListener("input", () => {
  if (search.value.trim()) mode = "modules";
  syncButtons();
  render();
});
groupFilter.addEventListener("change", () => {
  mode = groupFilter.value === "all" && !search.value.trim() ? "overview" : "modules";
  syncButtons();
  render();
});

function overviewGraph() {
  const cx = 600, cy = 380, rx = 430, ry = 250;
  const order = DATA.groups;
  const gnodes = order.map((g, i) => {
    const a = -Math.PI / 2 + (Math.PI * 2 * i) / order.length;
    return { id: g, label: g, group: g, count: DATA.groupCounts[g], x: cx + Math.cos(a) * rx, y: cy + Math.sin(a) * ry, r: 24 + Math.sqrt(DATA.groupCounts[g]) * 2.1, type: "group" };
  });
  const pos = new Map(gnodes.map(n => [n.id, n]));
  const gedges = DATA.groupEdges.filter(e => e.source !== e.target).map(e => ({ ...e, a: pos.get(e.source), b: pos.get(e.target) })).filter(e => e.a && e.b);
  return { nodes: gnodes, edges: gedges };
}

function moduleGraph() {
  const q = search.value.trim().toLowerCase();
  const group = groupFilter.value;
  let base = nodes.filter(n => (group === "all" || n.group === group) && (!q || n.id.toLowerCase().includes(q) || n.path.toLowerCase().includes(q)));
  if (!q && group === "all") base = [...nodes].sort((a, b) => (b.inDegree + b.outDegree) - (a.inDegree + a.outDegree)).slice(0, 120);
  if (base.length > 180) base = base.slice(0, 180);
  const ids = new Set(base.map(n => n.id));
  const cx = 600, cy = 380;
  const byGroup = new Map();
  for (const n of base) {
    if (!byGroup.has(n.group)) byGroup.set(n.group, []);
    byGroup.get(n.group).push(n);
  }
  const gnames = [...byGroup.keys()].sort();
  const drawn = [];
  for (const [gi, g] of gnames.entries()) {
    const list = byGroup.get(g).sort((a, b) => b.inDegree - a.inDegree || a.id.localeCompare(b.id));
    const gcx = cx + Math.cos((Math.PI * 2 * gi) / Math.max(1, gnames.length) - Math.PI / 2) * (gnames.length === 1 ? 0 : 280);
    const gcy = cy + Math.sin((Math.PI * 2 * gi) / Math.max(1, gnames.length) - Math.PI / 2) * (gnames.length === 1 ? 0 : 180);
    list.forEach((n, i) => {
      const cols = Math.ceil(Math.sqrt(list.length));
      const col = i % cols;
      const row = Math.floor(i / cols);
      drawn.push({ ...n, x: gcx + (col - cols / 2) * 50, y: gcy + (row - Math.ceil(list.length / cols) / 2) * 42, r: Math.max(7, Math.min(17, 7 + Math.sqrt(n.inDegree + n.outDegree))) });
    });
  }
  const pos = new Map(drawn.map(n => [n.id, n]));
  const medges = edges.filter(e => ids.has(e.source) && ids.has(e.target)).map(e => ({ ...e, a: pos.get(e.source), b: pos.get(e.target), count: 1 })).filter(e => e.a && e.b);
  return { nodes: drawn, edges: medges };
}

function focusGraph(id) {
  const center = byId.get(id);
  const imports = outgoing.get(id).slice().sort();
  const users = incoming.get(id).slice().sort();
  const gnodes = [{ ...center, x: 600, y: 380, r: 36, type: "module", role: "center", labelClass: "big" }];
  const left = radialModules(imports, 310, 380, 155, "import");
  gnodes.push(...left);
  const right = users.length > 22 ? groupedUserNodes(users) : radialModules(users, 900, 380, 210, "user");
  gnodes.push(...right);
  const pos = new Map(gnodes.map(n => [n.id, n]));
  const fedges = [
    ...imports.map(target => ({ source: id, target, a: pos.get(id), b: pos.get(target), count: 1, kind: "strong" })),
    ...(users.length > 22
      ? right.map(node => ({ source: node.id, target: id, a: node, b: pos.get(id), count: node.count, kind: "cluster" }))
      : users.map(source => ({ source, target: id, a: pos.get(source), b: pos.get(id), count: 1, kind: "reverse" }))),
  ].filter(e => e.a && e.b);
  return { nodes: gnodes, edges: fedges, focus: true, aggregated: users.length > 22 };
}

function radialModules(ids, cx, cy, radius, role) {
  if (!ids.length) return [];
  return ids.map((dep, i) => {
    const n = byId.get(dep);
    const spread = ids.length === 1 ? 0 : Math.PI * 1.15;
    const start = role === "import" ? Math.PI - spread / 2 : -spread / 2;
    const angle = start + (ids.length === 1 ? 0 : spread * i / (ids.length - 1));
    return {
      ...n,
      x: cx + Math.cos(angle) * radius,
      y: cy + Math.sin(angle) * radius,
      r: Math.max(10, Math.min(18, 9 + Math.sqrt(n.inDegree + n.outDegree))),
      type: "module",
      role,
      quietLabel: ids.length > 12
    };
  });
}

function groupedUserNodes(ids) {
  const grouped = new Map();
  for (const id of ids) {
    const n = byId.get(id);
    if (!grouped.has(n.group)) grouped.set(n.group, []);
    grouped.get(n.group).push(id);
  }
  const entries = [...grouped.entries()].sort((a, b) => b[1].length - a[1].length || a[0].localeCompare(b[0]));
  return entries.map(([group, members], i) => {
    const lane = i % 2;
    const row = Math.floor(i / 2);
    return {
      id: "cluster::" + group,
      label: group,
      group,
      members,
      count: members.length,
      x: 865 + lane * 145,
      y: 160 + row * 95,
      r: Math.max(24, Math.min(52, 20 + Math.sqrt(members.length) * 4.6)),
      type: "cluster",
      role: "user-cluster"
    };
  });
}

function render() {
  if (selected) currentGraph = focusGraph(selected);
  else currentGraph = mode === "overview" ? overviewGraph() : moduleGraph();
  visibleCount.textContent = currentGraph.nodes.length;
  renderResults();
  renderSvg();
  renderDetails();
}

function renderResults() {
  const q = search.value.trim().toLowerCase();
  const group = groupFilter.value;
  let list = nodes.filter(n => (group === "all" || n.group === group) && (!q || n.id.toLowerCase().includes(q) || n.path.toLowerCase().includes(q)));
  list = list.sort((a, b) => (b.inDegree + b.outDegree) - (a.inDegree + a.outDegree)).slice(0, 30);
  const box = document.querySelector("#results");
  box.innerHTML = list.length ? list.map(n => itemHtml(n.id, n.label, n.path, n.group)).join("") : '<div class="empty">No matching module.</div>';
  box.querySelectorAll(".item").forEach(btn => btn.addEventListener("click", () => {
    selected = btn.dataset.id;
    render();
  }));
}

function renderSvg() {
  const edgeHtml = currentGraph.edges.map(e => {
    const cls = e.kind === "strong" ? "edge strong" : e.kind === "reverse" ? "edge reverse" : e.kind === "cluster" ? "edge cluster" : "edge";
    const width = Math.min(7, 1 + Math.sqrt(e.count || 1));
    return '<line class="' + cls + '" x1="' + e.a.x + '" y1="' + e.a.y + '" x2="' + e.b.x + '" y2="' + e.b.y + '" style="stroke-width:' + width + '"></line>';
  }).join("");
  const nodeHtml = currentGraph.nodes.map(n => {
    const isSelected = selected === n.id;
    return '<circle class="node' + (isSelected ? " selected" : "") + (n.type === "cluster" ? " cluster" : "") + '" data-id="' + esc(n.id) + '" cx="' + n.x + '" cy="' + n.y + '" r="' + n.r + '" fill="' + color(n.group) + '"></circle>';
  }).join("");
  const labelHtml = currentGraph.nodes.map(n => labelForNode(n)).join("");
  svg.setAttribute("viewBox", view.x + " " + view.y + " " + view.w + " " + view.h);
  svg.innerHTML = '<defs><marker id="arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="5" markerHeight="5" orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="rgba(148,163,184,.7)"/></marker></defs><g>' + edgeHtml + '</g><g>' + nodeHtml + '</g><g>' + labelHtml + '</g>';
  svg.querySelectorAll(".node").forEach(el => {
    el.addEventListener("mouseenter", showTip);
    el.addEventListener("mousemove", moveTip);
    el.addEventListener("mouseleave", () => tip.style.display = "none");
    el.addEventListener("click", ev => {
      ev.stopPropagation();
      const id = el.dataset.id;
      if (byId.has(id)) selected = id;
      else if (id.startsWith("cluster::")) {
        groupFilter.value = id.slice("cluster::".length);
        search.value = "";
        mode = "modules";
        selected = null;
        syncButtons();
      }
      else {
        groupFilter.value = id;
        mode = "modules";
        selected = null;
        syncButtons();
      }
      render();
    });
  });
}

function labelForNode(n) {
  if (n.quietLabel) return "";
  const main = n.type === "cluster" ? n.label : n.label;
  const sub = n.type === "group" ? n.count + " files" : n.type === "cluster" ? n.count + " dependents" : n.role === "center" ? n.group : "";
  const cls = "label" + (n.labelClass ? " " + n.labelClass : "");
  const y = n.type === "cluster" ? n.y + 4 : n.y + n.r + 18;
  const subY = n.type === "cluster" ? n.y + n.r + 18 : n.y + n.r + 33;
  return '<text class="' + cls + '" x="' + n.x + '" y="' + y + '">' + esc(main) + '</text>' +
         (sub ? '<text class="sub-label" x="' + n.x + '" y="' + subY + '">' + esc(sub) + '</text>' : "");
}

function renderDetails() {
  if (!selected) {
    details.innerHTML = mode === "overview"
      ? '<div class="detail-title">Clean Overview</div><p>Each node is a GeoCoq area. Edge thickness means more imports between areas. Click an area to drill into its modules.</p>'
      : '<div class="detail-title">Module View</div><p>Showing matching modules. Use search or area filters to reduce noise, then click a module for a focused dependency neighborhood.</p>';
    return;
  }
  const n = byId.get(selected);
  const imports = outgoing.get(selected).map(id => byId.get(id)).sort((a, b) => a.id.localeCompare(b.id));
  const users = incoming.get(selected).map(id => byId.get(id)).sort((a, b) => a.id.localeCompare(b.id));
  const userGroups = groupSummary(users);
  details.innerHTML =
    '<div class="detail-title">' + esc(n.label) + '</div><p><code>' + esc(n.id) + '</code><br>' + esc(n.path) + '</p>' +
    '<div class="pills"><span class="pill">' + esc(n.group) + '</span><span class="pill">imports ' + imports.length + '</span><span class="pill">used by ' + users.length + '</span></div>' +
    (users.length > 22 ? '<p>Large reverse-dependency fan grouped by area in the graph. The full file list is below.</p><h2>Dependent Areas</h2>' + groupPills(userGroups) : "") +
    '<h2>Direct Imports</h2>' + depList(imports) + '<h2>Reverse Dependents</h2>' + depList(users);
}

function depList(list) {
  if (!list.length) return '<div class="empty">None inside GeoCoq.</div>';
  return '<div class="list">' + list.map(n => '<button class="dep-button" data-id="' + esc(n.id) + '">' + esc(n.id) + '</button>').join("") + '</div>';
}

function groupSummary(list) {
  const counts = new Map();
  for (const n of list) counts.set(n.group, (counts.get(n.group) || 0) + 1);
  return [...counts.entries()].sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]));
}

function groupPills(groups) {
  return '<div class="pills">' + groups.map(([g, count]) => '<span class="pill">' + esc(g) + ' ' + count + '</span>').join("") + '</div>';
}

details.addEventListener("click", ev => {
  const btn = ev.target.closest("[data-id]");
  if (!btn) return;
  selected = btn.dataset.id;
  render();
});

function showTip(ev) {
  const id = ev.currentTarget.dataset.id;
  const n = byId.get(id);
  if (n) {
    tip.innerHTML = '<b>' + esc(n.id) + '</b><code>' + esc(n.path) + '</code><br><span>imports ' + n.outDegree + ' · used by ' + n.inDegree + '</span>';
  } else if (id.startsWith("cluster::")) {
    const node = currentGraph.nodes.find(n => n.id === id);
    tip.innerHTML = '<b>' + esc(node.label) + '</b><span>' + node.count + ' files depend on the selected module. Click to open this area.</span>';
  } else {
    tip.innerHTML = '<b>' + esc(id) + '</b><span>' + DATA.groupCounts[id] + ' files</span>';
  }
  tip.style.display = "block";
  moveTip(ev);
}
function moveTip(ev) {
  tip.style.left = Math.min(window.innerWidth - 390, ev.clientX + 14) + "px";
  tip.style.top = Math.min(window.innerHeight - 130, ev.clientY + 14) + "px";
}

function zoom(factor) {
  const cx = view.x + view.w / 2;
  const cy = view.y + view.h / 2;
  view.w *= factor;
  view.h *= factor;
  view.x = cx - view.w / 2;
  view.y = cy - view.h / 2;
  renderSvg();
}
function resetView() {
  view = { x: 0, y: 0, w: 1200, h: 760 };
  renderSvg();
}
function focusSelected() {
  if (!selected) return resetView();
  view = { x: 180, y: 60, w: 840, h: 640 };
  renderSvg();
}
document.querySelector("#zoomIn").addEventListener("click", () => zoom(.78));
document.querySelector("#zoomOut").addEventListener("click", () => zoom(1.28));
document.querySelector("#resetView").addEventListener("click", resetView);
document.querySelector("#focusView").addEventListener("click", focusSelected);
svg.addEventListener("wheel", ev => {
  ev.preventDefault();
  zoom(ev.deltaY < 0 ? .86 : 1.16);
}, { passive: false });
svg.addEventListener("pointerdown", ev => {
  pan = { x: ev.clientX, y: ev.clientY, view: { ...view } };
  svg.setPointerCapture(ev.pointerId);
});
svg.addEventListener("pointermove", ev => {
  if (!pan) return;
  const dx = (ev.clientX - pan.x) * (view.w / svg.clientWidth);
  const dy = (ev.clientY - pan.y) * (view.h / svg.clientHeight);
  view.x = pan.view.x - dx;
  view.y = pan.view.y - dy;
  renderSvg();
});
svg.addEventListener("pointerup", () => pan = null);
svg.addEventListener("pointerleave", () => pan = null);

window.geoSelect = function(id) {
  if (!byId.has(id)) return false;
  selected = id;
  mode = "modules";
  syncButtons();
  render();
  focusSelected();
  return true;
};

const initialSelect = new URLSearchParams(location.search).get("select");
if (initialSelect && byId.has(initialSelect)) {
  selected = initialSelect;
  mode = "modules";
  syncButtons();
}
render();
if (selected) focusSelected();
</script>
</body>
</html>`;

fs.writeFileSync(outFile, html);
console.log(`Wrote ${path.relative(root, outFile)}`);
console.log(`${nodes.length} nodes, ${edges.length} internal GeoCoq edges, ${groups.length} groups`);
