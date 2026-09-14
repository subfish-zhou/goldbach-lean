/* Complete graphs are exported; only requested neighborhoods are rendered. */
"use strict";
(() => {
  const $ = id => document.getElementById(id);
  const state = {index: null, info: null, shards: new Map(), search: [], searchLoaded: false, searchPromise: null, route: 0};
  const edgeLabels = {type: "type Const", value: "proof / definition value Const", recursorRHS: "recursor RHS Const"};
  const el = (tag, text, cls) => {
    const node = document.createElement(tag);
    if (text !== undefined) node.textContent = text;
    if (cls) node.className = cls;
    return node;
  };
  const button = (text, action, cls) => {
    const node = el("button", text, cls); node.type = "button";
    node.addEventListener("click", () => Promise.resolve().then(action).catch(showError));
    return node;
  };
  const link = (text, href) => { const node = el("a", text); node.href = href; return node; };
  const showError = error => {
    console.error(error);
    $("detail").append(el("p", `Could not load this view: ${error.message}. Reload to retry.`, "error"));
  };
  async function get(path) {
    const response = await fetch(path);
    if (!response.ok) throw new Error(`${path}: HTTP ${response.status}`);
    const data = await response.json();
    if (data.schemaVersion !== 1) throw new Error(`Unsupported schema in ${path}`);
    return data;
  }
  async function shard(mid) {
    if (!state.shards.has(mid)) {
      const promise = get(state.index.modules[mid].shard).catch(error => { state.shards.delete(mid); throw error; });
      state.shards.set(mid, promise);
    }
    return state.shards.get(mid);
  }
  function navigate(mid, name) {
    const params = new URLSearchParams({module: String(mid)});
    if (name) params.set("decl", name);
    const hash = `#${params}`;
    if (location.hash === hash) route().catch(showError); else location.hash = hash;
  }
  function links(mid, declaration) {
    const module = state.index.modules[mid];
    const group = el("div", undefined, "links");
    group.append(link("Source at recorded commit", module.source));
    const api = declaration ? declaration.api : module.api;
    if (api) group.append(link("Lean API", api));
    else group.append(el("span", "No verified API anchor supplied; source fallback.", "muted"));
    return group;
  }
  function paginate(parent, items, render, size = 30) {
    let offset = 0;
    const more = button("", add, "more");
    function add() {
      more.remove();
      const stop = Math.min(offset + size, items.length);
      for (; offset < stop; offset++) parent.append(render(items[offset]));
      if (offset < items.length) { more.textContent = `Show ${Math.min(size, items.length - offset)} more (${items.length - offset} remaining)`; parent.append(more); }
    }
    add();
  }
  function lazy(summary, load) {
    const details = el("details"); details.append(el("summary", summary));
    let loaded = false;
    details.addEventListener("toggle", async () => {
      if (!details.open || loaded) return;
      loaded = true;
      const loading = el("p", "Loading…", "muted"); details.append(loading);
      try { details.append(await load()); loading.remove(); }
      catch (error) { loading.textContent = `Load failed: ${error.message}. Close and reopen to retry.`; loading.className = "error"; loaded = false; }
    });
    return details;
  }
  function importTree(ids, ancestors) {
    const list = el("ul", undefined, "tree");
    if (!ids.length) list.append(el("li", "No direct local imports.", "empty"));
    paginate(list, ids, mid => {
      const module = state.index.modules[mid], item = el("li");
      if (ancestors.has(mid)) { item.append(el("span", `↻ ${module.name} — already on this path`, "cycle")); return item; }
      item.append(lazy(`${module.name} (${module.imports.length} direct local imports)`, async () => {
        const body = el("div");
        body.append(button("Open module", () => navigate(mid)), links(mid));
        body.append(importTree(module.imports, new Set([...ancestors, mid])));
        if (module.externalImports.length) body.append(el("p", `External imports (not expanded): ${module.externalImports.join(", ")}`, "boundary"));
        return body;
      }));
      return item;
    });
    return list;
  }
  function references(data, declaration, ancestors) {
    const container = el("div");
    for (const [edge, label] of Object.entries(edgeLabels)) {
      const names = declaration.refs[edge];
      const local = names.filter(n => data.targets[n].scope === "local");
      const boundary = names.filter(n => data.targets[n].scope !== "local");
      container.append(el("h3", `${label}: ${names.length} references (${local.length} local, ${boundary.length} boundary)`));
      const list = el("ul", undefined, "tree");
      if (!names.length) list.append(el("li", "No Const references in this field.", "empty"));
      paginate(list, [...local, ...boundary], name => {
        const target = data.targets[name], item = el("li");
        if (target.scope !== "local") {
          item.className = "boundary";
          item.append(el("span", target.scope, "badge"), document.createTextNode(name));
          for (const mid of target.modules) item.append(link(` · ${state.index.modules[mid].name} source`, state.index.modules[mid].source));
          return item;
        }
        if (ancestors.has(name)) {
          item.append(el("span", `↻ ${name} — cycle / already on this dependency path`, "cycle"));
          for (const mid of target.modules) item.append(button(`Open in ${state.index.modules[mid].name}`, () => navigate(mid, name)));
          return item;
        }
        item.append(lazy(name, async () => {
          const body = el("div");
          if (target.modules.length > 1) body.append(el("p", `This name occurs in ${target.modules.length} actual module censuses (e.g. a regenerated equation lemma). All providers are retained; their reference signatures were checked equal.`, "muted"));
          for (const mid of target.modules) {
            const targetData = await shard(mid);
            const next = targetData.declarations.find(d => d.name === name);
            if (!next) throw new Error(`Missing local constant ${name}`);
            body.append(el("p", `Actual census provider: ${state.index.modules[mid].name} · ${next.kind}`, "muted"));
            body.append(button("Focus this declaration", () => navigate(mid, name)), links(mid, next));
            body.append(lazy("Expand this provider's direct Const references", async () => references(targetData, next, new Set([...ancestors, name]))));
          }
          return body;
        }));
        return item;
      });
      container.append(list);
    }
    return container;
  }
  async function route() {
    if (!state.index) return;
    const params = new URLSearchParams(location.hash.slice(1));
    if (!params.has("module")) return;
    const text = params.get("module");
    if (!/^\d+$/.test(text || "")) throw new Error("Invalid module route");
    const mid = Number(text), module = state.index.modules[mid];
    if (!module) throw new Error("Unknown module ID");
    const ticket = ++state.route;
    $("detail").replaceChildren(el("p", "Loading module shard…"));
    const data = await shard(mid);
    if (ticket !== state.route) return;
    const name = params.get("decl");
    const detail = $("detail"); detail.replaceChildren();
    if (name) {
      const declaration = data.declarations.find(d => d.name === name);
      if (!declaration) throw new Error("Declaration not present in this module's constNames");
      detail.append(el("span", declaration.kind, "badge"), el("h2", name));
      detail.append(el("p", `Actual constNames owner: ${module.name}`, "muted"));
      detail.append(button("Back to owning module", () => navigate(mid)), links(mid, declaration));
      if (declaration.cycle !== null) {
        const row = state.index.cycles[declaration.cycle];
        const note = el("div", undefined, "cycle");
        note.append(lazy(`Recursive reference cluster ${row.id} · ${row.size} declarations (edges retained)`, async () => {
          const cycle = await get(row.shard), body = el("div");
          paginate(body, cycle.members.flatMap(([member, owners]) => owners.map(owner => [member, owner])), ([member, owner]) => button(`${member} · ${state.index.modules[owner].name}`, () => navigate(owner, member), "result"));
          return body;
        }));
        detail.append(note);
      }
      detail.append(references(data, declaration, new Set([name])));
    } else {
      detail.append(el("span", "Module import view — not a theorem dependency graph", "badge"), el("h2", module.name), links(mid));
      detail.append(el("h3", "Public endpoint Const-closure roles"));
      const roles = Array.isArray(module.proofRoles) ? module.proofRoles : null;
      detail.append(el("p", roles === null ? "Unavailable — this export does not supply proofRoles." : roles.length ? roles.join(" · ") : "Library-only / outside displayed endpoint Const closures", "proof-roles"));
      detail.append(el("p", "A role means at least one declaration in this module's actual constNames belongs to that displayed public endpoint's Const closure. It does not mean the whole module is consumed. Module imports below are a separate relation.", "muted"));
      detail.append(el("h3", `Direct local imports (${module.imports.length})`), importTree(module.imports, new Set([mid])));
      detail.append(el("p", `External module imports (not expanded): ${module.externalImports.join(", ") || "none"}`, "boundary"));
      detail.append(el("h3", `Compiled declarations (${data.declarations.length})`));
      const list = el("div");
      paginate(list, data.declarations, d => button(`${d.name} · ${d.kind}`, () => navigate(mid, d.name), "result"), 40);
      detail.append(list);
      if (data.extraConstNames.length) detail.append(el("p", `${data.extraConstNames.length} extraConstNames metadata entries; these do not imply available declaration bodies.`, "boundary"));
    }
  }
  async function loadSearch() {
    if (state.searchLoaded) return;
    if (state.searchPromise) return state.searchPromise;
    state.searchPromise = (async () => {
      let cursor = 0, finished = 0;
      const groups = state.index.searchShards, results = new Array(groups.length);
      async function worker() {
        while (cursor < groups.length) {
          const i = cursor++, data = await get(groups[i].path);
          results[i] = data.declarations; finished++;
          $("search-status").textContent = `Loading complete declaration search: ${finished}/${groups.length} index shards…`;
        }
      }
      await Promise.all(Array.from({length: Math.min(4, groups.length)}, worker));
      state.search = results.flat(); state.searchLoaded = true;
    })().catch(error => { state.searchPromise = null; throw error; });
    return state.searchPromise;
  }
  async function search() {
    const mode = $("search-mode").value;
    if (mode === "declarations") await loadSearch();
    // Read controls after asynchronous loading, so stale queries never overwrite newer ones.
    const query = $("query").value.trim().toLowerCase(), library = $("library").value;
    if ($("search-mode").value !== mode) return;
    const rows = mode === "modules" ? state.index.modules.map(m => [m.name, m.id, "module"]) : state.search;
    const found = rows.filter(([name, mid]) => name.toLowerCase().includes(query) && (!library || state.index.modules[mid].library === library));
    $("search-status").textContent = `${found.length.toLocaleString()} matches in ${rows.length.toLocaleString()} ${mode === "declarations" ? "declaration records (all census providers)" : "modules"}. Results are paginated.`;
    $("results").replaceChildren();
    paginate($("results"), found, ([name, mid, kind]) => {
      const result = button(name, () => navigate(mid, mode === "declarations" ? name : null), "result");
      result.append(el("small", `${kind} · ${state.index.modules[mid].library}`)); return result;
    });
  }
  async function loadProjection() {
    const data = await get("blueprint-projection.json"), labels = new Map(data.nodes.map(n => [n.label, n]));
    const body = $("projection"); body.replaceChildren();
    for (const node of data.nodes) {
      body.append(lazy(`${node.title} · ${node.chapter}`, async () => {
        const row = el("div", undefined, "projection-row");
        node.modules.forEach(mid => row.append(button(`Open actual declaration: ${node.name}`, () => navigate(mid, node.name), "result")));
        const incoming = data.edges.filter(([, b]) => b === node.label).map(([a]) => labels.get(a));
        const outgoing = data.edges.filter(([a]) => a === node.label).map(([, b]) => labels.get(b));
        for (const [title, nodes] of [["Authored prerequisites", incoming], ["Authored consumers", outgoing]]) {
          row.append(el("h3", `${title} (${nodes.length})`));
          nodes.forEach(n => n.modules.forEach(mid => row.append(button(n.title, () => navigate(mid, n.name), "result"))));
        }
        row.append(el("p", "This selection's edges are explanatory, not asserted to be the direct compiled Const edges. Open the declaration to inspect those separately.", "muted"));
        return row;
      }));
    }
    $("load-projection").hidden = true;
  }
  async function init() {
    [state.index, state.info] = await Promise.all([get("modules.json"), get("build-info.json")]);
    const info = state.info;
    const referenceCount = Object.values(info.const_reference_counts).reduce((a, b) => a + b, 0);
    $("build-status").textContent = `${info.module_count.toLocaleString()} modules · ${info.declaration_count.toLocaleString()} compiled declarations · ${info.module_import_edge_count.toLocaleString()} direct local imports · ${referenceCount.toLocaleString()} typed Const references · source ${info.source_revision.slice(0, 12)}`;
    $("projection-count").textContent = `Blueprint: ${info.blueprint_node_count} selected nodes and ${info.blueprint_edge_count} authored edges. Complete compiled graph: ${info.declaration_count.toLocaleString()} declarations, including ${info.declarations_in_cycles} declarations in ${info.cyclic_declaration_components} recursive reference clusters. These are different relations and different coverage, not interchangeable counts.`;
    for (const entry of state.index.entries) {
      const card = el("div", undefined, "entry"); card.append(el("h3", entry.label));
      card.append(button("Explore module imports", () => navigate(entry.module)));
      if (entry.declaration) entry.declarationModules.forEach(mid => card.append(button("Explore theorem Const references", () => navigate(mid, entry.declaration))));
      card.append(el("p", `${entry.reachableModuleCountIncludingEntry} local modules in the import closure (including entry).`));
      if (entry.declaration) card.append(el("p", `${entry.reachableDeclarationCountIncludingEntry} declarations in this theorem's local Const closure (including theorem). Not the same relation.`));
      $("entries").append(card);
    }
    let timer;
    $("query").addEventListener("input", () => { clearTimeout(timer); timer = setTimeout(() => search().catch(showError), 140); });
    for (const id of ["search-mode", "library"]) $(id).addEventListener("change", () => search().catch(showError));
    $("load-projection").addEventListener("click", () => loadProjection().catch(showError));
    window.addEventListener("hashchange", () => route().catch(showError));
    await search(); await route();
  }
  init().catch(error => { $("build-status").textContent = "Explorer could not load. Serve the site over HTTP(S), not file://."; showError(error); });
})();
