// Proof vs. Search: client for the local API. No external libraries (works offline).
"use strict";

const $ = (id) => document.getElementById(id);
const esc = (s) => String(s ?? "").replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));

async function api(path, opts = {}) {
  const r = await fetch(path, opts.body ? { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(opts.body) } : opts);
  const text = await r.text();
  if (!r.ok) {
    let msg = text;
    try { msg = JSON.parse(text).detail ?? text; } catch (_) { /* plain text */ }
    throw new Error(typeof msg === "string" ? msg : JSON.stringify(msg));
  }
  try { return JSON.parse(text); } catch (_) { return text; }
}

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
function markdown(src, base) {
  const lines = src.replace(/\r/g, "").split("\n");
  let html = "", i = 0;
  while (i < lines.length) {
    const l = lines[i];
    if (l.startsWith("```")) {
      const buf = [];
      i++;
      while (i < lines.length && !lines[i].startsWith("```")) buf.push(lines[i++]);
      i++;
      html += `<pre><code>${esc(buf.join("\n"))}</code></pre>`;
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

// ---------- navigation ----------
function show(view) {
  document.querySelectorAll(".view").forEach((v) => (v.hidden = v.id !== `view-${view}`));
  document.querySelectorAll("#nav button").forEach((b) => b.classList.toggle("active", b.dataset.view === view));
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
    else $("doc").innerHTML = `<h1>${esc(path)}</h1><pre><code>${esc(text)}</code></pre>`;
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
let designs = [];
function renderVerdicts(rows) {
  const body = rows.sort((a, b) => (a.property + a.side + (a.task || "")).localeCompare(b.property + b.side + (b.task || "")))
    .map((r) => {
      const where = r.side === "mc" ? `${esc(r.task)}: ${esc(r.engine)}` : esc(r.note || "lean");
      const depth = r.side === "lean" && r.status === "proved" ? "∞" : (r.depth ?? "");
      const ev = r.cex_vcd ? `<button class="cex" data-vcd="${esc(r.cex_vcd)}">counterexample</button>` :
        r.side === "lean" ? esc(trusts(r.axioms || [])) : "engine";
      return `<tr><td><code>${esc(r.property)}</code></td><td><span class="side-tag">${r.side === "mc" ? "MC" : "Lean"}</span></td>
        <td>${where}</td><td class="v-${esc(r.status)}">${esc(r.status)}</td><td class="num">${depth}</td>
        <td class="num">${r.time_s ?? ""}s</td><td>${ev}</td></tr>`;
    }).join("");
  $("verdicts").innerHTML = `<thead><tr><th>property</th><th>side</th><th>task / theorem</th><th>verdict</th><th>depth</th><th>time</th><th>trusts / evidence</th></tr></thead><tbody>${body}</tbody>`;
}
function trusts(ax) {
  const std = new Set(["propext", "Classical.choice", "Quot.sound"]);
  const extra = ax.filter((a) => !std.has(a)).map((a) => a.includes("._native.bv_decide") ? "bv_decide" : a.includes("._native.") ? "native_decide" : a);
  return "kernel" + (extra.length ? " + " + [...new Set(extra)].join(", ") : "");
}
async function viewFile(path, title) {
  $("viewer-title").textContent = title || path;
  const md = path.endsWith(".md");
  $("viewer").hidden = md; $("viewer-md").hidden = !md;
  try {
    const text = await api(`/api/file?path=${encodeURIComponent(path)}`);
    if (md) $("viewer-md").innerHTML = markdown(text); else $("viewer").textContent = text;
  } catch (e) { $("viewer").hidden = false; $("viewer-md").hidden = true; $("viewer").textContent = e.message; }
}
function selectDesign(name) {
  const d = designs.find((x) => x.name === name);
  if (!d) return;
  const files = [["README", d.readme], ...d.rtl.map((f) => [f.split("/").pop(), f]), ["SymbiYosys", d.sby],
    ["generated Lean", d.generated], ["Lean solution", d.solution], ["Lean exercise", d.exercise]].filter((f) => f[1]);
  $("files").innerHTML = files.map(([t, p]) => `<button data-file="${esc(p)}">${esc(t)}</button>`).join("");
  api(`/api/designs/${name}/last`).then(renderVerdicts).catch(() => {
    $("verdicts").innerHTML = `<tbody><tr><td class="muted">No saved run yet. "Run both sides" takes a few seconds per SymbiYosys task.</td></tr></tbody>`;
  });
  viewFile(d.readme, "README");
}
$("files").addEventListener("click", (e) => { if (e.target.dataset.file) viewFile(e.target.dataset.file); });
$("verdicts").addEventListener("click", async (e) => {
  const vcd = e.target.dataset.vcd;
  if (!vcd) return;
  $("viewer-title").textContent = "Counterexample, per step";
  $("viewer").hidden = false; $("viewer-md").hidden = true;
  try { $("viewer").textContent = await api(`/api/cex?path=${encodeURIComponent(vcd)}`); }
  catch (err) { $("viewer").textContent = err.message; }
});
$("design-select").addEventListener("change", (e) => selectDesign(e.target.value));
$("run-design").addEventListener("click", async () => {
  const name = $("design-select").value, btn = $("run-design");
  btn.disabled = true; $("run-note").textContent = "running SymbiYosys tasks and checking Lean theorems…";
  const t0 = performance.now();
  try { renderVerdicts(await api(`/api/designs/${name}/run`, { method: "POST" })); $("run-note").textContent = `done in ${((performance.now() - t0) / 1000).toFixed(1)} s`; }
  catch (e) { $("run-note").textContent = e.message; }
  btn.disabled = false;
});

// ---------- Lean scratchpad ----------
$("lean-check").addEventListener("click", async () => {
  const btn = $("lean-check"); btn.disabled = true; $("lean-note").textContent = "compiling…";
  try {
    const r = await api("/api/lean/check", { body: { code: $("lean-code").value } });
    $("lean-note").textContent = r.ok ? (r.uses_sorry ? "compiles, but uses sorry" : "compiles") : `${r.errors.length} error(s)`;
    $("lean-out").textContent = r.output || "(no messages)";
  } catch (e) { $("lean-note").textContent = e.message; }
  btn.disabled = false;
});

// ---------- SAT lab ----------
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

// ---------- tutor ----------
$("tutor-ask").addEventListener("click", async () => {
  const btn = $("tutor-ask"); btn.disabled = true; $("tutor-note").textContent = "thinking…";
  try {
    const r = await api("/api/tutor", { body: { question: $("tutor-q").value, level: +$("tutor-level").value, file: $("tutor-file").value || null } });
    $("tutor-out").innerHTML = markdown(r.text); $("tutor-note").textContent = `tools used: ${r.tools.join(", ") || "none"}`;
  } catch (e) { $("tutor-note").textContent = e.message; }
  btn.disabled = false;
});

// ---------- start ----------
(async () => {
  const st = await api("/api/status").catch(() => ({}));
  const flag = (k, label) => `${label} <b>${st[k] ? "✓" : "–"}</b>`;
  $("status").innerHTML = [flag("lean", "Lean"), flag("sby", "SymbiYosys"), flag("ibex", "Ibex"), flag("tutor", "tutor")].join(" · ");
  if (!st.tutor) { $("tutor-ask").disabled = true; $("tutor-note").textContent = "unavailable: no ANTHROPIC_API_KEY on the server"; }
  const docs = await api("/api/docs-list");
  $("doc-select").innerHTML = docs.map((d) => `<option value="${esc(d.path)}">${esc(d.title)}</option>`).join("");
  openDoc("course/README.md");
  designs = await api("/api/designs");
  $("design-select").innerHTML = designs.map((d) => `<option value="${esc(d.name)}">${esc(d.name)}</option>`).join("");
  if (designs.length) selectDesign(designs[0].name);
})();
