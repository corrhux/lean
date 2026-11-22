// Proof vs. Search: client for the local API. No external libraries (works offline).
"use strict";

const $ = (id) => document.getElementById(id);
const esc = (s) => String(s ?? "").replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
const store = {                          // per-viewer conveniences only; the app works without it
  get(k) { try { return JSON.parse(localStorage.getItem(k)); } catch (_) { return null; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (_) { /* private mode */ } },
  del(k) { try { localStorage.removeItem(k); } catch (_) { /* private mode */ } },
};

async function api(path, opts = {}) {
  const init = opts.body !== undefined
    ? { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(opts.body) } : opts;
  const r = await fetch(path, init);
  const text = await r.text();
  if (!r.ok) {
    let msg = text;
    try { msg = JSON.parse(text).detail ?? text; } catch (_) { /* plain text */ }
    throw new Error(typeof msg === "string" ? msg : JSON.stringify(msg));
  }
  try { return JSON.parse(text); } catch (_) { return text; }
}
const debounce = (fn, ms) => { let t; return (...a) => { clearTimeout(t); t = setTimeout(() => fn(...a), ms); }; };

// ---------- minimal Markdown (headings, lists, tables, code, emphasis, links) ----------
function inline(s) {
  return esc(s)
    .replace(/`([^`]+)`/g, "<code>$1</code>")
    .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
    .replace(/(^|[^*])\*([^*\s][^*]*)\*/g, "$1<em>$2</em>")
    .replace(/\[([^\]]+)\]\(([^)\s]+)\)/g, (_, t, href) => {
      if (/^https?:/.test(href)) return `<a href="${href}" target="_blank" rel="noopener">${t}</a>`;
      return `<a href="#" data-doc="${href}">${t}</a>`;
    });
}
function markdown(src) {
  const lines = src.replace(/\r/g, "").split("\n");
  let html = "", i = 0;
  while (i < lines.length) {
    const l = lines[i];
    if (l.startsWith("```")) {
      const lang = l.slice(3).trim(), buf = [];
      i++;
      while (i < lines.length && !lines[i].startsWith("```")) buf.push(lines[i++]);
      i++;
      const code = buf.join("\n");
      html += `<pre><code>${/^lean|^(system)?verilog|^sv$/.test(lang) ? highlight(code, lang.startsWith("lean") ? "lean" : "sv") : esc(code)}</code></pre>`;
      continue;
    }
    const h = l.match(/^(#{1,4})\s+(.*)/);
    if (h) { html += `<h${h[1].length}>${inline(h[2])}</h${h[1].length}>`; i++; continue; }
    if (/^\|/.test(l)) {
      const rows = [];
      while (i < lines.length && /^\|/.test(lines[i])) rows.push(lines[i++]);
      const cells = (r) => r.replace(/^\||\|$/g, "").split(/(?<!\\)\|/).map((c) => c.trim());
      const body = rows.filter((r) => !/^\|[\s:|-]+\|?$/.test(r));
      html += "<table>" + body.map((r, k) => "<tr>" + cells(r).map((c) => k === 0 ? `<th>${inline(c)}</th>` : `<td>${inline(c)}</td>`).join("") + "</tr>").join("") + "</table>";
      continue;
    }
    if (/^\s*([-*]|\d+\.)\s+/.test(l)) {
      const ordered = /^\s*\d+\./.test(l), items = [];
      while (i < lines.length && /^\s*([-*]|\d+\.)\s+/.test(lines[i])) {
        let item = lines[i++].replace(/^\s*([-*]|\d+\.)\s+/, "");
        while (i < lines.length && /^\s{2,}\S/.test(lines[i]) && !/^\s*([-*]|\d+\.)\s+/.test(lines[i])) item += " " + lines[i++].trim();
        items.push(`<li>${inline(item)}</li>`);
      }
      html += ordered ? `<ol>${items.join("")}</ol>` : `<ul>${items.join("")}</ul>`;
      continue;
    }
    if (l.startsWith(">")) {
      const buf = [];
      while (i < lines.length && lines[i].startsWith(">")) buf.push(lines[i++].replace(/^>\s?/, ""));
      html += `<blockquote>${inline(buf.join(" "))}</blockquote>`;
      continue;
    }
    if (l.trim() === "" || /^---+$/.test(l.trim())) { i++; continue; }
    const buf = [];
    while (i < lines.length && lines[i].trim() !== "" && !/^(#|```|\||>|\s*([-*]|\d+\.)\s)/.test(lines[i])) buf.push(lines[i++]);
    html += `<p>${inline(buf.join(" "))}</p>`;
  }
  return html;
}
function resolveDoc(base, href) {
  if (href.startsWith("#")) return null;
  const parts = base.split("/").slice(0, -1);
  for (const seg of href.split("#")[0].split("/")) {
    if (seg === "..") parts.pop(); else if (seg && seg !== ".") parts.push(seg);
  }
  return parts.join("/");
}

// ---------- syntax highlighting (Lean 4 and SystemVerilog) ----------
const LEAN_KW = "theorem lemma def abbrev structure inductive where namespace end section open import variable example by fun let have show from at with match if then else do return instance class deriving calc intro intros exact apply refine simp simp_all simp_arith omega decide bv_decide native_decide rfl cases rcases induction constructor unfold rw rwa sorry set_option in private noncomputable termination_by decreasing_by obtain use exists ext funext contradiction assumption trivial split next all_goals any_goals first repeat try norm_num subst specialize generalize revert clear exfalso left right this Type Prop".split(" ");
const SV_KW = "module endmodule input output inout logic wire reg bit always_ff always_comb always_latch always assign if else case casez casex endcase begin end parameter localparam assert assume cover property posedge negedge initial typedef enum struct packed default for genvar generate endgenerate function endfunction return unique priority import package endpackage int integer signed unsigned".split(" ");
const HL = {
  lean: new RegExp(String.raw`(--[^\n]*|\/-[\s\S]*?-\/)|("(?:[^"\\\n]|\\.)*")|(\b\d+(?:#\d+)?\b)|\b(${LEAN_KW.join("|")})\b|([∀∃→←↔∧∨¬⊢λ⟨⟩≠≤≥])`, "g"),
  sv: new RegExp(String.raw`(\/\/[^\n]*|\/\*[\s\S]*?\*\/)|("(?:[^"\\\n]|\\.)*")|(\b\d*'[sS]?[bodhBODH][0-9a-fA-F_xzXZ]+|\b\d+\b)|\b(${SV_KW.join("|")})\b|(\$\w+)`, "g"),
};
function highlight(code, lang) {
  const re = HL[lang] || HL.lean;
  let out = "", last = 0;
  re.lastIndex = 0;
  for (let m; (m = re.exec(code));) {
    out += esc(code.slice(last, m.index));
    const cls = m[1] ? "cm" : m[2] ? "str" : m[3] ? "num" : m[4] ? "kw" : "sym";
    out += `<span class="hl-${cls}">${esc(m[0])}</span>`;
    last = re.lastIndex;
  }
  return out + esc(code.slice(last));
}

// ---------- code editor: a transparent textarea over a highlighted <pre> ----------
const LH = 20; // line height in px, matches the CSS
function makeEditor(el, { lang = "lean", value = "" } = {}) {
  el.classList.add("editor");
  el.innerHTML = `<div class="ed-gutter"></div><div class="ed-body"><div class="ed-marks"></div><pre class="ed-hl" aria-hidden="true"></pre><textarea spellcheck="false" autocapitalize="off" autocomplete="off" aria-label="code"></textarea></div>`;
  const ta = el.querySelector("textarea"), hl = el.querySelector("pre"), gut = el.querySelector(".ed-gutter"), marks = el.querySelector(".ed-marks");
  const ed = { onChange: null, onCursor: null, diags: [] };
  function render() {
    hl.innerHTML = highlight(ta.value, lang) + "\n";
    const n = ta.value.split("\n").length, worst = new Map();
    for (const d of ed.diags) {
      if (d.severity !== "error" && d.severity !== "warning") continue;
      for (let l = d.line; l <= Math.min(d.endLine, d.line + 40); l++) if (worst.get(l) !== "error") worst.set(l, d.severity);
    }
    gut.innerHTML = Array.from({ length: n }, (_, i) => `<div class="${worst.has(i) ? "g-" + worst.get(i) : ""}">${i + 1}</div>`).join("") + "<div></div>";
    marks.innerHTML = ed.diags.filter((d) => d.severity === "error" || d.severity === "warning").map((d) => {
      const w = d.endLine > d.line ? Math.max(4, (ta.value.split("\n")[d.line] || "").length - d.col) : Math.max(1, d.endCol - d.col);
      return `<div class="sq sq-${d.severity}" style="top:${8 + d.line * LH + LH - 3}px;left:calc(10px + ${d.col}ch);width:${w}ch"></div>`;
    }).join("");
    syncScroll();
  }
  function syncScroll() {
    hl.scrollTop = ta.scrollTop; hl.scrollLeft = ta.scrollLeft; gut.scrollTop = ta.scrollTop;
    marks.style.transform = `translate(${-ta.scrollLeft}px, ${-ta.scrollTop}px)`;
  }
  function pos() {
    const before = ta.value.slice(0, ta.selectionStart);
    const line = before.split("\n").length - 1;
    return { line, character: before.length - before.lastIndexOf("\n") - 1 };
  }
  const cursor = () => ed.onCursor && ed.onCursor(pos());
  ta.addEventListener("input", () => { render(); ed.onChange && ed.onChange(ta.value); cursor(); });
  ta.addEventListener("scroll", syncScroll);
  ta.addEventListener("keyup", (e) => { if (!e.key.startsWith("Shift")) cursor(); });
  ta.addEventListener("click", cursor);
  ta.addEventListener("keydown", (e) => {
    if (e.key === "Tab" && !e.shiftKey) { e.preventDefault(); ta.setRangeText("  ", ta.selectionStart, ta.selectionEnd, "end"); ta.dispatchEvent(new Event("input")); }
  });
  Object.defineProperty(ed, "value", {     // an accessor: Object.assign would copy a snapshot
    get() { return ta.value; },
    set(v) { ta.value = v; ed.diags = []; render(); },
  });
  Object.assign(ed, {
    setDiagnostics(d) { ed.diags = d; render(); },
    goto(line) {
      const lines = ta.value.split("\n");
      const off = lines.slice(0, line).reduce((a, l) => a + l.length + 1, 0);
      ta.focus(); ta.setSelectionRange(off, off);
      ta.scrollTop = Math.max(0, line * LH - ta.clientHeight / 3); syncScroll(); cursor();
    },
    pos,
  });
  ed.value = value;
  return ed;
}

// ---------- live Lean: diagnostics as you type, goals at the cursor ----------
function leanLive({ editor, key, msgsEl, goalsEl, statusEl, extra }) {
  let seq = 0, syncing = Promise.resolve(), lastGoal = null, cur = { line: 0, character: 0 };
  const live = { diagnostics: [], goalText: "", stale: true };
  function renderMsgs(r) {
    const model = (r.model_diagnostics || []).filter((d) => d.severity === "error");
    msgsEl.innerHTML = model.map((d) => `<div class="msg error">regenerated model, line ${d.line + 1}: ${esc(d.message)}</div>`).join("") +
      r.diagnostics.map((d, k) => `<div class="msg ${d.severity}" data-k="${k}">line ${d.line + 1}: ${esc(d.message)}</div>`).join("");
  }
  async function sync() {
    const my = ++seq;
    statusEl.textContent = live.everSynced ? "checking…" : "starting Lean and loading the imports (the first time can take a minute)…";
    const p = api("/api/lean/sync", { body: { key, code: editor.value, ...(extra ? extra() : {}) } });
    syncing = p.catch(() => {});
    try {
      const r = await p;
      if (my !== seq) return;
      live.everSynced = true; live.stale = false;
      live.diagnostics = r.diagnostics;
      editor.setDiagnostics(r.diagnostics);
      renderMsgs(r);
      const errs = r.diagnostics.filter((d) => d.severity === "error").length;
      const sorry = r.diagnostics.some((d) => /declaration uses 'sorry'|declaration uses `sorry`/.test(d.message));
      statusEl.textContent = (errs ? `${errs} error(s)` : sorry ? "no errors, but uses sorry" : "no errors") +
        ` · ${r.seconds}s` + (r.regenerated ? " · model regenerated from your RTL" : "");
      goal();
    } catch (e) { if (my === seq) statusEl.textContent = e.message; }
  }
  async function goal() {
    await syncing;
    const p = { ...cur };
    try {
      const r = await api("/api/lean/goal", { body: { key, ...p } });
      lastGoal = r;
      const here = live.diagnostics.filter((d) => d.line <= p.line && p.line <= d.endLine);
      let html = `<h3>Line ${p.line + 1}, column ${p.character + 1}</h3>`;
      if (r.goals) html += r.goals.length ? r.goals.map((g, i) => `<h3>${r.goals.length > 1 ? `Goal ${i + 1} of ${r.goals.length}` : "Goal"}</h3><pre>${highlight(g, "lean")}</pre>`).join("") : (here.some((d) => d.severity === "error") ? `<h3>Goals</h3><p class="muted">None shown: Lean stopped this proof at the error below.</p>` : `<h3>Goals</h3><pre>No goals: this proof is done.</pre>`);
      if (r.term) html += `<h3>Expected type</h3><pre>${highlight(r.term, "lean")}</pre>`;
      if (!r.goals && !r.term) html += `<p class="muted">Put the cursor inside a proof (after <code>by</code>) to see what is left to prove.</p>`;
      if (here.length) html += `<h3>Messages</h3>` + here.map((d) => `<pre>${esc(d.message)}</pre>`).join("");
      goalsEl.innerHTML = html;
      live.goalText = (r.goals || []).join("\n\n") + (r.term ? `\nExpected type: ${r.term}` : "");
    } catch (e) { goalsEl.innerHTML = `<p class="muted">${esc(e.message)}</p>`; }
  }
  const later = debounce(sync, 500), goalLater = debounce(goal, 200);
  editor.onChange = () => { live.stale = true; later(); };
  editor.onCursor = (p) => { cur = p; goalLater(); };
  msgsEl.addEventListener("click", (e) => {
    const k = e.target.closest(".msg")?.dataset.k;
    if (k !== undefined) editor.goto(live.diagnostics[+k].line);
  });
  goalsEl.innerHTML = `<p class="muted">Goals appear here.</p>`;
  live.sync = sync;
  return live;
}

// ---------- navigation ----------
let currentView = "course", workView = "lean";   // workView: where the tutor's context comes from
function show(view) {
  currentView = view;
  if (view === "twins" || view === "lean" || view === "exam") workView = view;
  document.querySelectorAll(".view").forEach((v) => (v.hidden = v.id !== `view-${view}`));
  document.querySelectorAll("#nav button").forEach((b) => b.classList.toggle("active", b.dataset.view === view));
  if (view === "lean" && scratch.stale) scratch.sync();
  if (view === "exam") loadExam();
  if (view === "tutor") $("tutor-context-note").textContent = contextLabel();
}
$("nav").addEventListener("click", (e) => { if (e.target.dataset.view) show(e.target.dataset.view); });

// ---------- course ----------
let currentDoc = "course/README.md";
async function openDoc(path) {
  currentDoc = path;
  $("doc-select").value = path;
  try {
    const text = await api(`/api/file?path=${encodeURIComponent(path)}`);
    if (path.endsWith(".md")) $("doc").innerHTML = markdown(text);
    else $("doc").innerHTML = `<h1>${esc(path)}</h1><pre><code>${highlight(text, path.endsWith(".sv") ? "sv" : "lean")}</code></pre>`;
  } catch (e) { $("doc").innerHTML = `<p class="muted">${esc(e.message)}</p>`; }
  window.scrollTo(0, 0);
}
$("doc").addEventListener("click", (e) => {
  const a = e.target.closest("a[data-doc]");
  if (!a) return;
  e.preventDefault();
  const target = resolveDoc(currentDoc, a.dataset.doc);
  if (target) {
    if (!$("doc-select").querySelector(`option[value="${CSS.escape(target)}"]`)) {
      $("doc-select").insertAdjacentHTML("beforeend", `<option value="${esc(target)}">${esc(target)}</option>`);
    }
    openDoc(target);
  }
});
$("doc-select").addEventListener("change", (e) => openDoc(e.target.value));

// ---------- twin labs ----------
let designs = [], twin = null;         // twin: state of the selected design's workspace
const rtlEditor = makeEditor($("rtl-editor"), { lang: "sv" });
const twinLeanEditor = makeEditor($("twin-lean-editor"), { lang: "lean" });
const twinLean = leanLive({
  editor: twinLeanEditor, key: "twin", msgsEl: $("twin-lean-msgs"), goalsEl: $("twin-lean-goals"), statusEl: $("twin-lean-status"),
  extra: () => ({ design: twin.name, rtl: editedRtl() }),
});
function editedRtl() {
  const out = {};
  for (const [f, text] of Object.entries(twin.rtl)) if (text !== twin.base.rtl[f]) out[f] = text;
  return out;
}
function isEdited() { return Object.keys(editedRtl()).length > 0 || twin.solution !== twin.base.solution; }
function saveEdits() {
  const edited = isEdited();
  $("edit-note").hidden = $("reset-edits").hidden = !edited;
  if (edited) store.set(`pvs.edits.${twin.name}`, { rtl: editedRtl(), solution: twin.solution !== twin.base.solution ? twin.solution : null });
  else store.del(`pvs.edits.${twin.name}`);
}
let twinTab = "verdicts";
function showTab(tab) {
  twinTab = tab;
  document.querySelectorAll("#twin-tabs button").forEach((b) => b.classList.toggle("active", b.dataset.tab === tab));
  document.querySelectorAll("#view-twins .pane").forEach((p) => (p.hidden = p.dataset.pane !== tab));
  if (tab === "lean" && twinLean.stale) twinLean.sync();
  if (tab === "bench") loadBench();
}
$("twin-tabs").addEventListener("click", (e) => { if (e.target.dataset.tab) showTab(e.target.dataset.tab); });

function renderVerdicts(rows) {
  const body = rows.sort((a, b) => (a.property + a.side + (a.task || "")).localeCompare(b.property + b.side + (b.task || "")))
    .map((r) => {
      const where = r.side === "mc" ? `${esc(r.task)}: ${esc(r.engine)}` : esc((r.note || "lean").split(":")[0]);
      const depth = r.side === "lean" && r.status === "proved" ? "∞" : (r.depth ?? "");
      let ev;
      if (r.cex_vcd) ev = `<button class="cex" data-vcd="${esc(r.cex_vcd)}" data-label="${esc(`${r.property}, ${r.task}`)}">${r.status === "inconclusive" ? "induction trace" : "counterexample"}</button>`;
      else if (r.side === "lean" && (r.status === "proved" || r.status === "sorry")) ev = esc(trusts(r.axioms || []));
      else if (r.side === "lean" || r.status === "error") ev = `<span class="muted">${esc((r.note || "").split(": ").slice(1).join(": ") || r.note || "")}</span>`;
      else ev = r.note ? `<span class="muted">${esc(r.note)}</span>` : "engine";
      return `<tr><td><code>${esc(r.property)}</code></td><td><span class="side-tag">${r.side === "mc" ? "MC" : "Lean"}</span></td>
        <td>${where}</td><td class="v-${esc(r.status)}">${esc(r.status)}</td><td class="num">${depth}</td>
        <td class="num">${r.time_s ?? ""}s</td><td>${ev}</td></tr>`;
    }).join("");
  $("verdicts").innerHTML = `<thead><tr><th>property</th><th>side</th><th>task / theorem</th><th>verdict</th><th>depth</th><th>time</th><th>trusts / evidence</th></tr></thead><tbody>${body}</tbody>`;
}
function trusts(ax) {
  const std = new Set(["propext", "Classical.choice", "Quot.sound"]);
  const extra = ax.filter((a) => !std.has(a)).map((a) => a.includes("._native.bv_decide") ? "bv_decide" : a.includes("._native.") ? "native_decide" : a === "sorryAx" ? "sorry" : a);
  return "kernel" + (extra.length ? " + " + [...new Set(extra)].join(", ") : "");
}
async function viewFile(path, title) {
  $("viewer-title").textContent = title || path;
  const md = path.endsWith(".md");
  $("viewer").hidden = md; $("viewer-md").hidden = !md;
  try {
    const text = await api(`/api/file?path=${encodeURIComponent(path)}`);
    if (md) $("viewer-md").innerHTML = markdown(text);
    else $("viewer").innerHTML = highlight(text, /\.(sv|v|sby)$/.test(path) ? "sv" : "lean");
  } catch (e) { $("viewer").hidden = false; $("viewer-md").hidden = true; $("viewer").textContent = e.message; }
}
async function selectDesign(name) {
  const d = designs.find((x) => x.name === name);
  if (!d) return;
  store.set("pvs.design", name);
  const base = await api(`/api/designs/${name}/workspace`);
  const saved = store.get(`pvs.edits.${name}`) || {};
  twin = { name, d, base, rtl: { ...base.rtl, ...(saved.rtl || {}) }, solution: saved.solution ?? base.solution, file: Object.keys(base.rtl)[0] };
  $("rtl-file").innerHTML = Object.keys(base.rtl).map((f) => `<option>${esc(f)}</option>`).join("");
  rtlEditor.value = twin.rtl[twin.file];
  twinLeanEditor.value = twin.solution;
  $("twin-lean-path").textContent = base.solution_path;
  twinLean.stale = true; $("twin-lean-msgs").innerHTML = ""; $("twin-lean-status").textContent = "";
  saveEdits();
  const files = [["README", d.readme], ...d.rtl.map((f) => [f.split("/").pop(), f]), ["SymbiYosys", d.sby],
    ["generated Lean", d.generated], ["Lean solution", d.solution], ["Lean exercise", d.exercise]].filter((f) => f[1]);
  $("files").innerHTML = files.map(([t, p]) => `<button data-file="${esc(p)}">${esc(t)}</button>`).join("");
  viewFile(d.readme, "README");
  api(`/api/designs/${name}/last`).then(renderVerdicts).catch(() => {
    $("verdicts").innerHTML = `<tbody><tr><td class="muted">No saved run yet. "Run both sides" takes a few seconds per SymbiYosys task.</td></tr></tbody>`;
  });
  benchLoadedFor = null;
  if (twinTab === "lean") twinLean.sync();
  if (twinTab === "bench") loadBench();
}
$("rtl-file").addEventListener("change", (e) => { twin.file = e.target.value; rtlEditor.value = twin.rtl[twin.file]; });
rtlEditor.onChange = (v) => { twin.rtl[twin.file] = v; twinLean.stale = true; saveEdits(); };
const twinLeanChange = twinLeanEditor.onChange;
twinLeanEditor.onChange = (v) => { twin.solution = v; saveEdits(); twinLeanChange(v); };
$("reset-edits").addEventListener("click", () => {
  if (!confirm("Discard your edits to this design's RTL and Lean solution?")) return;
  store.del(`pvs.edits.${twin.name}`);
  selectDesign(twin.name);
});
$("files").addEventListener("click", (e) => { if (e.target.dataset.file) viewFile(e.target.dataset.file); });
$("verdicts").addEventListener("click", (e) => {
  const b = e.target.closest("button.cex");
  if (b) { showTab("wave"); showWave(b.dataset.vcd, b.dataset.label); }
});
$("design-select").addEventListener("change", (e) => selectDesign(e.target.value));
$("run-design").addEventListener("click", async () => {
  const btn = $("run-design");
  btn.disabled = true;
  const edited = isEdited();
  $("run-note").textContent = edited ? "running SymbiYosys on your RTL and Lean on your solution…" : "running SymbiYosys tasks and checking Lean theorems…";
  const t0 = performance.now();
  try {
    const body = edited ? { rtl: editedRtl(), solution: twin.solution !== twin.base.solution ? twin.solution : null } : undefined;
    renderVerdicts(await api(`/api/designs/${twin.name}/run`, body ? { body } : { method: "POST" }));
    $("run-note").textContent = `done in ${((performance.now() - t0) / 1000).toFixed(1)} s` + (edited ? " (your edited version)" : "");
    showTab("verdicts");
  } catch (e) { $("run-note").textContent = e.message; }
  btn.disabled = false;
});

// ---------- waveform viewer ----------
let wave = null, waveCursor = 0;
async function showWave(path, label) {
  $("wave-title").textContent = label || path;
  $("wave").innerHTML = `<p class="muted">loading…</p>`;
  try {
    wave = await api(`/api/vcd?path=${encodeURIComponent(path)}`);
    waveCursor = Math.max(0, wave.steps - 1);
    drawWave();
    $("wave-table").textContent = await api(`/api/cex?path=${encodeURIComponent(path)}`);
  } catch (e) { $("wave").innerHTML = `<p class="muted">${esc(e.message)}</p>`; }
}
function fmtVal(v, width) {
  if (v == null) return "?";
  if (!/^[01]+$/.test(v)) return v;
  const n = BigInt("0b" + v);
  return width > 8 ? "0x" + n.toString(16) : n.toString();
}
function drawWave() {
  if (!wave) return;
  const internal = $("wave-internal").checked;
  // one sample per clock period, so the clock itself carries no information: hide it with the tool signals
  const sigs = wave.signals.filter((s) => internal || !/^(smt_|\$|clk$|clock$)|_EN$/.test(s.short));
  const STEP = 46, ROW = 28, TOP = 24, n = wave.steps, W = n * STEP + 4, H = TOP + sigs.length * ROW + 6;
  let names = `<svg class="names" width="210" height="${H}"><text x="10" y="16" class="dim">signal = value at step ${waveCursor}</text>`;
  let lanes = `<svg width="${W}" height="${H}">`;
  for (let k = 0; k <= n; k++) lanes += `<line class="grid" x1="${k * STEP}" y1="${TOP - 6}" x2="${k * STEP}" y2="${H}"/>` + (k < n ? `<text x="${k * STEP + STEP / 2}" y="16" text-anchor="middle" class="dim">${k}</text>` : "");
  sigs.forEach((s, r) => {
    const y0 = TOP + r * ROW, hi = y0 + 5, lo = y0 + ROW - 7, mid = (hi + lo) / 2;
    names += `<text x="10" y="${mid + 4}">${esc(s.short.length > 16 ? s.short.slice(0, 15) + "…" : s.short)}<tspan class="dim"> = ${esc(fmtVal(s.values[waveCursor], s.width))}</tspan></text>`;
    if (s.width === 1) {
      let d = "", prevY = null;
      s.values.forEach((v, k) => {
        if (v !== "0" && v !== "1") { lanes += `<rect class="xz" x="${k * STEP}" y="${hi}" width="${STEP}" height="${lo - hi}"/>`; prevY = null; return; }
        const y = v === "1" ? hi : lo;
        d += prevY === null ? `M${k * STEP},${y}` : (prevY !== y ? `L${k * STEP},${prevY}L${k * STEP},${y}` : "");
        d += `L${(k + 1) * STEP},${y}`;
        prevY = y;
      });
      if (d) lanes += `<path class="w1" d="${d}"/>`;
    } else {
      let k = 0;
      while (k < n) {
        let j = k;
        while (j + 1 < n && s.values[j + 1] === s.values[k]) j++;
        const x0 = k * STEP + 2, x1 = (j + 1) * STEP - 2, v = s.values[k];
        const shape = `M${x0},${mid}L${x0 + 4},${hi}L${x1 - 4},${hi}L${x1},${mid}L${x1 - 4},${lo}L${x0 + 4},${lo}Z`;
        lanes += `<path class="${v && /^[01]+$/.test(v) ? "bus" : "bus xz"}" d="${shape}"/>`;
        const label = fmtVal(v, s.width);
        if (label.length * 7.3 < x1 - x0 - 8) lanes += `<text x="${(x0 + x1) / 2}" y="${mid + 4}" text-anchor="middle">${esc(label)}</text>`;
        k = j + 1;
      }
    }
  });
  lanes += `<line class="cursor" x1="${waveCursor * STEP + STEP / 2}" y1="${TOP - 4}" x2="${waveCursor * STEP + STEP / 2}" y2="${H}"/>`;
  for (let k = 0; k < n; k++) lanes += `<rect class="hit" data-step="${k}" x="${k * STEP}" y="0" width="${STEP}" height="${H}"><title>step ${k}</title></rect>`;
  $("wave").innerHTML = names + "</svg>" + `<div class="lanes">${lanes}</svg></div>`;
}
$("wave").addEventListener("click", (e) => { const k = e.target.dataset?.step; if (k !== undefined) { waveCursor = +k; drawWave(); } });
$("wave-internal").addEventListener("change", drawWave);

// ---------- benchmark chart ----------
let benchLoadedFor = null;
function loadBench() {
  if (!twin || benchLoadedFor === twin.name) return;
  benchLoadedFor = twin.name;
  const b = twin.d.bench;
  $("bench-run").disabled = !b;
  $("bench-chart").innerHTML = ""; $("bench-table").innerHTML = ""; $("bench-note").textContent = "";
  if (!b) { $("bench-about").textContent = "This design has no parameter sweep."; return; }
  $("bench-about").innerHTML = `Sweeps <code>${esc(b.param)}</code> over ${esc(b.values.join(", "))}: one SymbiYosys run (${esc(b.engine)}, ${esc(b.mode || "bmc")}) per value, next to one Lean theorem, <code>${esc(b.all_values_theorem || "")}</code>, that covers every value at once.`;
  api(`/api/designs/${twin.name}/bench/last`).then(drawBench).catch(() => { $("bench-note").textContent = "No saved sweep yet."; });
}
$("bench-run").addEventListener("click", async () => {
  const btn = $("bench-run"); btn.disabled = true;
  $("bench-note").textContent = "sweeping: one model-checking run per value, then the Lean theorem…";
  try { drawBench(await api(`/api/designs/${twin.name}/bench`, { body: { timeout: +$("bench-timeout").value } })); $("bench-note").textContent = ""; }
  catch (e) { $("bench-note").textContent = e.message; }
  btn.disabled = false;
});
function drawBench(res) {
  const pts = res.rows.filter((r) => r.value !== "all"), lean = res.rows.find((r) => r.value === "all");
  const param = res.bench.param;
  $("bench-table").innerHTML = `<thead><tr><th>${esc(param)}</th><th>engine</th><th>result</th><th>time</th></tr></thead><tbody>` +
    res.rows.map((r) => `<tr><td>${esc(r.value === "all" ? "every value" : r.value)}</td><td>${esc(r.engine)}</td><td class="v-${esc(r.status)}">${esc(r.status)}</td><td class="num">${r.time_s.toFixed(2)} s</td></tr>`).join("") + "</tbody>";
  const el = $("bench-chart");
  const W = Math.max(360, el.clientWidth || 720), H = 300, m = { l: 58, r: 150, t: 14, b: 44 };
  const pw = W - m.l - m.r, ph = H - m.t - m.b;
  const times = res.rows.map((r) => r.time_s).filter((t) => t > 0);
  const lo = Math.pow(10, Math.floor(Math.log10(Math.min(...times, 0.5)))), hi = Math.pow(10, Math.ceil(Math.log10(Math.max(...times) * 1.05)));
  const y = (t) => m.t + ph - (Math.log10(Math.max(t, lo)) - Math.log10(lo)) / (Math.log10(hi) - Math.log10(lo)) * ph;
  const x = (i) => m.l + (pts.length === 1 ? pw / 2 : (i / (pts.length - 1)) * pw);
  let s = `<svg viewBox="0 0 ${W} ${H}" role="img" aria-label="Benchmark: time per ${esc(param)} for model checking, and one Lean proof for every value">`;
  for (let d = lo; d <= hi * 1.001; d *= 10) {
    s += `<line class="grid" x1="${m.l}" x2="${m.l + pw}" y1="${y(d)}" y2="${y(d)}"/><text x="${m.l - 8}" y="${y(d) + 4}" text-anchor="end">${d < 1 ? d.toFixed(1) : d.toFixed(0)} s</text>`;
  }
  s += `<line class="axis" x1="${m.l}" x2="${m.l + pw}" y1="${m.t + ph}" y2="${m.t + ph}"/>`;
  pts.forEach((p, i) => { s += `<text x="${x(i)}" y="${m.t + ph + 18}" text-anchor="middle">${esc(p.value)}</text>`; });
  s += `<text x="${m.l + pw / 2}" y="${H - 6}" text-anchor="middle">${esc(param)}</text>`;
  const ok = pts.map((p, i) => [p, i]).filter(([p]) => p.status !== "TIMEOUT");
  if (ok.length > 1) s += `<path class="s1" d="${ok.map(([p, i], k) => `${k ? "L" : "M"}${x(i)},${y(p.time_s)}`).join("")}"/>`;
  if (lean) {
    s += `<path class="s2" d="M${m.l},${y(lean.time_s)}L${m.l + pw},${y(lean.time_s)}"/>`;
    s += `<text class="lbl" x="${m.l + pw + 8}" y="${y(lean.time_s) + 4}">Lean: ${lean.time_s.toFixed(1)} s, every ${esc(param)}</text>`;
    s += `<rect class="hit" x="${m.l}" y="${y(lean.time_s) - 8}" width="${pw}" height="16" data-tip="${esc(`Lean, ${lean.theorem || "theorem"}: proved once for every ${param} in ${lean.time_s.toFixed(2)} s (load + check)`)}"/>`;
  }
  pts.forEach((p, i) => {
    const t = p.status === "TIMEOUT";
    s += `<circle class="d1${t ? " open" : ""}" cx="${x(i)}" cy="${y(p.time_s)}" r="5"/>`;
    if (t) s += `<text class="lbl" x="${x(i)}" y="${y(p.time_s) - 10}" text-anchor="middle">timeout</text>`;
    s += `<circle class="hit" cx="${x(i)}" cy="${y(p.time_s)}" r="14" data-tip="${esc(`${param} = ${p.value}: ${p.status} in ${p.time_s.toFixed(2)} s (${p.engine})`)}"/>`;
  });
  const last = ok[ok.length - 1];
  if (last) s += `<text class="lbl" x="${m.l + pw + 8}" y="${y(last[0].time_s) + (lean && Math.abs(y(last[0].time_s) - y(lean.time_s)) < 16 ? -10 : 4)}">model checking, per ${esc(param)}</text>`;
  s += "</svg>";
  el.innerHTML = `<div class="legend"><span><i style="background:var(--series-1)"></i>model checking: one run per value</span><span><i style="background:var(--series-2)"></i>Lean: one theorem for every value</span></div>` + s;
}
document.addEventListener("mousemove", (e) => {
  const t = e.target.closest?.("[data-tip]"), tip = $("tip");
  if (!t) { tip.hidden = true; return; }
  tip.textContent = t.dataset.tip; tip.hidden = false;
  tip.style.left = Math.min(e.clientX + 14, innerWidth - 330) + "px"; tip.style.top = e.clientY + 14 + "px";
});

// ---------- Lean scratchpad ----------
const SCRATCH_DEFAULT = `import RtlProof
import Std.Tactic.BVDecide

-- Move the cursor into a proof to see its goal on the right.
theorem xor_cancel (x y : BitVec 32) : (x ^^^ y) ^^^ y = x := by
  bv_decide

theorem add_zero_right (x : BitVec 8) (h : x ≤ 9#8) : x + 0#8 ≤ 9#8 := by
  simp
  exact h

#print axioms xor_cancel

-- A false claim: bv_decide answers with a counterexample, like a CEX.
-- example (x : BitVec 8) : x + 1#8 > x := by bv_decide
`;
const scratchEditor = makeEditor($("scratch-editor"), { lang: "lean", value: store.get("pvs.scratch") || SCRATCH_DEFAULT });
const scratch = leanLive({ editor: scratchEditor, key: "scratch", msgsEl: $("scratch-msgs"), goalsEl: $("scratch-goals"), statusEl: $("scratch-status") });
const scratchChange = scratchEditor.onChange;
// The workbook: the scratchpad (kept in the browser) or one of your exercise/exam files (saved to the repo).
let wb = { files: [], current: "", texts: {}, dirty: false };
scratchEditor.onChange = (v) => {
  if (wb.current) { wb.texts[wb.current] = v; wb.dirty = true; $("wb-note").textContent = "unsaved changes"; }
  else store.set("pvs.scratch", v);
  scratchChange(v);
};
async function loadWorkbook() {
  wb.files = await api("/api/workbook");
  for (const f of wb.files) wb.texts[f.path] = f.text;
  $("wb-file").innerHTML = `<option value="">Scratchpad</option>` +
    wb.files.map((f) => `<option value="${esc(f.path)}">${esc(f.title)} (${esc(f.path)})</option>`).join("");
}
function openWorkbook(path) {
  wb.current = path; wb.dirty = false;
  $("wb-file").value = path;
  const f = wb.files.find((x) => x.path === path);
  $("wb-save").hidden = !path; $("wb-solution").hidden = !(f && f.solution);
  $("wb-note").textContent = path ? "" : "not saved to the repository";
  scratchEditor.value = path ? wb.texts[path] : (store.get("pvs.scratch") || SCRATCH_DEFAULT);
  scratch.sync();
}
$("wb-file").addEventListener("change", (e) => {
  if (wb.dirty && !confirm("You have unsaved changes in this file. Switch anyway?")) { $("wb-file").value = wb.current; return; }
  openWorkbook(e.target.value);
});
$("wb-save").addEventListener("click", async () => {
  try {
    await api("/api/workbook/save", { body: { path: wb.current, text: wb.texts[wb.current] } });
    wb.dirty = false; $("wb-note").textContent = `saved ${wb.current}`;
  } catch (e) { $("wb-note").textContent = e.message; }
});
$("wb-solution").addEventListener("click", () => {
  const f = wb.files.find((x) => x.path === wb.current);
  if (f && f.solution && confirm("Open the solution? Try the exercise first; the tutor gives graded hints.")) {
    show("course"); openDoc(f.solution);
  }
});

// ---------- Ibex exam ----------
let exam = null, examPart = "MultDiv";
const examEditor = makeEditor($("exam-editor"), { lang: "lean" });
const examLive = leanLive({ editor: examEditor, key: "exam", msgsEl: $("exam-msgs"), goalsEl: $("exam-goals"),
  statusEl: $("exam-status") });
const examChange = examEditor.onChange;
examEditor.onChange = (v) => { exam.texts[examPart] = v; $("exam-note").textContent = "unsaved changes"; examChange(v); };
async function loadExam() {
  if (exam) { if (examLive.stale) examLive.sync(); return; }
  const r = await api("/api/exam");
  exam = { items: r.items, paths: {}, texts: {} };
  for (const p of r.parts) { exam.paths[p.name] = p.path; exam.texts[p.name] = p.text; }
  $("exam-part").innerHTML = r.parts.map((p) => `<option value="${esc(p.name)}">${esc(p.path)}</option>`).join("");
  examEditor.value = exam.texts[examPart];
  examLive.sync();
}
$("exam-part").addEventListener("change", (e) => {
  examPart = e.target.value; examEditor.value = exam.texts[examPart]; examLive.sync();
});
async function examSave() {
  await api("/api/exam/save", { body: { part: examPart, text: exam.texts[examPart] } });
  $("exam-note").textContent = `saved ${exam.paths[examPart]}`;
}
$("exam-save").addEventListener("click", () => examSave().catch((e) => { $("exam-note").textContent = e.message; }));
$("exam-grade").addEventListener("click", async () => {
  const btn = $("exam-grade"); btn.disabled = true;
  try {
    await examSave();
    $("exam-note").textContent = "grading…";
    const r = await api("/api/exam/grade", { method: "POST" });
    $("exam-score").innerHTML = "<thead><tr><th>item</th><th>points</th><th>status</th><th>notes</th></tr></thead><tbody>" +
      r.items.map((i) => `<tr><td>${esc(i.title)}</td><td class="num">${i.points ? `${i.score}/${i.points}` : "bonus"}</td>
        <td class="v-${esc(i.status)}">${esc(i.status)}</td><td class="muted">${esc(i.detail || (i.status === "proved" ? "kernel + bv_decide" : ""))}</td></tr>`).join("") +
      `</tbody>`;
    $("exam-note").textContent = `score ${r.score} / ${r.total}` + (r.tampered.length ? ` · UNOFFICIAL: ${r.tampered.join(", ")} changed` : "");
  } catch (e) { $("exam-note").textContent = e.message; }
  btn.disabled = false;
});
$("exam-prep").addEventListener("click", (e) => { e.preventDefault(); show("course"); openDoc("docs/CAPSTONE_EXAM_PREP.md"); });

// ---------- SAT lab: the five labs, then the zoo ----------
api("/api/satlab/labs").then((labs) => {
  $("lab-select").innerHTML = labs.map((l) => `<option value="${l.lab}">Lab ${l.lab}: ${esc(l.title)}</option>`).join("");
}).catch(() => {});
$("lab-run").addEventListener("click", async () => {
  const btn = $("lab-run"); btn.disabled = true; $("lab-note").textContent = "running… (Lab 3 compares eight solvers and takes about a minute)";
  try {
    const r = await api("/api/satlab/lab", { body: { lab: +$("lab-select").value } });
    $("lab-out").innerHTML = r.steps.map((s) => `<h3 class="muted"><code>$ ${esc(s.command)}</code> <span>(${s.seconds} s)</span></h3><pre class="code">${esc(s.output || "(no output)")}</pre>`).join("");
    $("lab-note").textContent = `Lab ${r.lab} done`;
  } catch (e) { $("lab-note").textContent = e.message; }
  btn.disabled = false;
});

$("sat-run").addEventListener("click", async () => {
  const btn = $("sat-run"); btn.disabled = true; $("sat-note").textContent = "solving…";
  try {
    const r = await api("/api/satlab/zoo", { body: { kind: $("sat-kind").value, width: +$("sat-width").value, n: +$("sat-n").value, timeout: +$("sat-timeout").value } });
    $("sat-note").textContent = `${r.vars} variables, ${r.clauses} clauses`;
    $("sat-table").innerHTML = "<thead><tr><th>solver</th><th>result</th><th>time</th><th>conflicts</th><th>decisions</th><th>about</th></tr></thead><tbody>" +
      r.rows.map((x) => `<tr><td><code>${esc(x.solver)}</code></td><td class="v-${esc(x.result)}">${esc(x.result)}</td><td class="num">${x.time_s}s</td>
        <td class="num">${x.conflicts ?? ""}</td><td class="num">${x.decisions ?? ""}</td><td class="muted">${esc(x.about)}</td></tr>`).join("") + "</tbody>";
  } catch (e) { $("sat-note").textContent = e.message; }
  btn.disabled = false;
});

// ---------- tutor (streamed, bound to what you are working on) ----------
function workingOn() {
  if (twin && workView === "twins") {
    const diags = twinLean.diagnostics.map((d) => `line ${d.line + 1} ${d.severity}: ${d.message}`).join("\n");
    return {
      label: `twin lab "${twin.name}" (${twinTab} tab)`,
      file: twin.base.solution_path,
      text: [`Twin lab: ${twin.name}. Edited RTL files: ${Object.keys(editedRtl()).join(", ") || "none"}.`,
        ...Object.entries(editedRtl()).map(([f, t]) => `My edited ${f}:\n\`\`\`systemverilog\n${t}\n\`\`\``),
        `My Lean solution (${twin.base.solution_path}):\n\`\`\`lean\n${twin.solution}\n\`\`\``,
        diags && `Lean messages:\n${diags}`, twinLean.goalText && `Goal at my cursor:\n${twinLean.goalText}`].filter(Boolean).join("\n\n"),
    };
  }
  if (exam && workView === "exam") {
    const diags = examLive.diagnostics.map((d) => `line ${d.line + 1} ${d.severity}: ${d.message}`).join("\n");
    return {
      label: `the Ibex exam (${exam.paths[examPart]})`, file: null,
      text: [`I am working on the Ibex exam, file ${exam.paths[examPart]} (statements in RtlProof/Exam/Ibex/Statements.lean). ` +
        "Teach; do not give me a complete proof unless the hint level is 5.",
        `My file:\n\`\`\`lean\n${examEditor.value}\n\`\`\``, diags && `Lean messages:\n${diags}`,
        examLive.goalText && `Goal at my cursor:\n${examLive.goalText}`].filter(Boolean).join("\n\n"),
    };
  }
  const diags = scratch.diagnostics.map((d) => `line ${d.line + 1} ${d.severity}: ${d.message}`).join("\n");
  return {
    label: wb.current ? wb.current : "the Lean scratchpad", file: null,
    text: [wb.current ? `I am working on ${wb.current}. Teach; do not give me the whole proof unless the hint level is 5.` : "",
      `My Lean ${wb.current ? "file" : "scratchpad"}:\n\`\`\`lean\n${scratchEditor.value}\n\`\`\``, diags && `Lean messages:\n${diags}`,
      scratch.goalText && `Goal at my cursor:\n${scratch.goalText}`].filter(Boolean).join("\n\n"),
  };
}
function contextLabel() { return `(${workingOn().label})`; }
$("tutor-ask").addEventListener("click", async () => {
  const btn = $("tutor-ask"); btn.disabled = true;
  $("tutor-note").textContent = "thinking…"; $("tutor-out").innerHTML = ""; $("tutor-tools").innerHTML = "";
  const ctx = $("tutor-context").checked ? workingOn() : null;
  let text = "";
  try {
    const r = await fetch("/api/tutor/stream", { method: "POST", headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ question: $("tutor-q").value, level: +$("tutor-level").value, file: ctx?.file || null, context: ctx?.text?.slice(0, 60000) || null }) });
    if (!r.ok) { let m = await r.text(); try { m = JSON.parse(m).detail; } catch (_) { /* text */ } throw new Error(m); }
    const reader = r.body.getReader(), dec = new TextDecoder();
    let buf = "";
    for (;;) {
      const { value, done } = await reader.read();
      if (done) break;
      buf += dec.decode(value, { stream: true });
      let i;
      while ((i = buf.indexOf("\n\n")) >= 0) {
        const line = buf.slice(0, i).split("\n").find((l) => l.startsWith("data: "));
        buf = buf.slice(i + 2);
        if (!line) continue;
        const ev = JSON.parse(line.slice(6));
        if (ev.type === "text") { text += ev.text; $("tutor-out").innerHTML = markdown(text); }
        else if (ev.type === "round") { if (text) text += "\n\n"; }
        else if (ev.type === "tool") $("tutor-tools").insertAdjacentHTML("beforeend", `<span>${esc(ev.label)}</span>`);
        else if (ev.type === "done") $("tutor-note").textContent = `${ev.model || ""} · ${ev.output_tokens} output tokens`;
        else if (ev.type === "error") $("tutor-note").textContent = ev.message;
      }
    }
  } catch (e) { $("tutor-note").textContent = e.message; }
  btn.disabled = false;
});

// ---------- start ----------
(async () => {
  const st = await api("/api/status").catch(() => ({}));
  const flag = (k, label) => `${label} <b>${st[k] ? "✓" : "–"}</b>`;
  $("status").innerHTML = [flag("lean", "Lean"), flag("sby", "SymbiYosys"), flag("ibex", "Ibex"), flag("tutor", "tutor")].join(" · ");
  if (!st.tutor) { $("tutor-ask").disabled = true; $("tutor-note").textContent = "unavailable: no ANTHROPIC_API_KEY on the server"; }
  loadWorkbook().catch(() => {});
  const docs = await api("/api/docs-list");
  $("doc-select").innerHTML = docs.map((d) => `<option value="${esc(d.path)}">${esc(d.title)}</option>`).join("");
  openDoc("course/README.md");
  designs = await api("/api/designs");
  $("design-select").innerHTML = designs.map((d) => `<option value="${esc(d.name)}">${esc(d.name)}</option>`).join("");
  const last = store.get("pvs.design");
  const first = designs.some((d) => d.name === last) ? last : designs[0]?.name;
  if (first) { $("design-select").value = first; selectDesign(first); }
})();
