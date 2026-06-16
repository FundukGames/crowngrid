/*
 * Zip puzzle engine.
 * --------------------------------------------------------------------------
 * Draw one continuous path that fills EVERY cell exactly once, passing through
 * the numbered checkpoints 1, 2, 3 … in order (a Hamiltonian path with ordered
 * waypoints). The generator builds a random Hamiltonian path, places numbered
 * checkpoints on it, then adds just enough for the solution to be unique
 * (verified by a backtracking counter with a strong connectivity prune: a
 * single path can never cover disconnected unvisited regions). Framework-free;
 * attaches window.Zip.
 */
(function () {
  "use strict";

  function mulberry32(seed) {
    let a = seed >>> 0;
    return function () {
      a |= 0; a = (a + 0x6d2b79f5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function shuffle(arr, rng) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  // Precompute neighbor lists for the grid.
  function buildAdj(n) {
    const adj = [];
    for (let idx = 0; idx < n * n; idx++) {
      const r = (idx / n) | 0, c = idx % n, out = [];
      if (r > 0) out.push(idx - n);
      if (r < n - 1) out.push(idx + n);
      if (c > 0) out.push(idx - 1);
      if (c < n - 1) out.push(idx + 1);
      adj.push(out);
    }
    return adj;
  }

  // Are all currently-unvisited cells one connected region? (BFS)
  function unvisitedConnected(adj, visited, total, stack, seen) {
    let start = -1, count = 0;
    for (let i = 0; i < total; i++) if (!visited[i]) { count++; if (start < 0) start = i; }
    if (count === 0) return true;
    let top = 0; stack[top++] = start; seen[start] = 1;
    let reached = 1;
    while (top > 0) {
      const x = stack[--top];
      const nb = adj[x];
      for (let j = 0; j < nb.length; j++) {
        const y = nb[j];
        if (!visited[y] && seen[y] !== 1) { seen[y] = 1; stack[top++] = y; reached++; }
      }
    }
    for (let i = 0; i < total; i++) if (!visited[i]) seen[i] = 0; // reset
    return reached === count;
  }

  function buildHamiltonian(n, rng, adj) {
    const total = n * n;
    const visited = new Array(total).fill(false);
    const seen = new Int8Array(total);
    const stack = new Int32Array(total);
    const path = [];

    function dfs(cur) {
      visited[cur] = true; path.push(cur);
      if (path.length === total) return true;
      if (unvisitedConnected(adj, visited, total, stack, seen)) {
        for (const nb of shuffle(adj[cur].slice(), rng)) {
          if (!visited[nb] && dfs(nb)) return true;
        }
      }
      visited[cur] = false; path.pop();
      return false;
    }
    for (const s of shuffle([...Array(total).keys()], rng)) {
      visited.fill(false); path.length = 0;
      if (dfs(s)) return path;
    }
    return null;
  }

  // Count solutions up to `limit`: paths from 1, ending at k, hitting numbers
  // in order. Node-capped so it can never hang.
  function countSolutions(n, num, k, limit, adj, cap) {
    cap = cap || 400000;
    const total = n * n;
    const start = num.indexOf(1);
    const visited = new Array(total).fill(false);
    const seen = new Int8Array(total);
    const stack = new Int32Array(total);
    let result = 0, nodes = 0, aborted = false;

    function dfs(cur, count, expected) {
      if (result >= limit || aborted) return;
      if (++nodes > cap) { aborted = true; return; }
      visited[cur] = true;
      if (num[cur] === k) {                 // k is terminal
        if (count === total) result++;
        visited[cur] = false; return;
      }
      if (count < total && !unvisitedConnected(adj, visited, total, stack, seen)) {
        visited[cur] = false; return;
      }
      const nb = adj[cur];
      for (let j = 0; j < nb.length; j++) {
        const y = nb[j];
        if (visited[y]) continue;
        if (num[y] !== 0 && num[y] !== expected) continue;
        dfs(y, count + 1, num[y] === expected ? expected + 1 : expected);
        if (result >= limit || aborted) break;
      }
      visited[cur] = false;
    }
    dfs(start, 1, 2);
    return aborted ? limit : result;
  }

  function numbersFrom(path, positions) {
    const num = new Array(path.length).fill(0);
    positions.forEach((p, i) => { num[path[p]] = i + 1; });
    return num;
  }

  function generate(opts) {
    opts = opts || {};
    const n = opts.size || 6;
    const rng = typeof opts.seed === "number" ? mulberry32(opts.seed) : Math.random;
    const total = n * n;
    const adj = buildAdj(n);

    for (let attempt = 0; attempt < 30; attempt++) {
      const path = buildHamiltonian(n, rng, adj);
      if (!path) continue;

      // Seed checkpoints (endpoints + evenly spaced); ~1 every 5 cells.
      const clues = Math.max(4, Math.round(total / 5));
      const posSet = new Set([0, total - 1]);
      for (let i = 1; i < clues - 1; i++) posSet.add(Math.round(i * (total - 1) / (clues - 1)));
      let positions = [...posSet].sort((a, b) => a - b);
      let num = numbersFrom(path, positions);

      // Add a checkpoint at the midpoint of the largest gap until unique.
      let guard = 0;
      while (countSolutions(n, num, positions.length, 2, adj) !== 1 && guard < total) {
        guard++;
        let gi = 0, gap = -1;
        for (let i = 0; i + 1 < positions.length; i++) {
          if (positions[i + 1] - positions[i] > gap) { gap = positions[i + 1] - positions[i]; gi = i; }
        }
        const mid = Math.floor((positions[gi] + positions[gi + 1]) / 2);
        if (mid === positions[gi] || mid === positions[gi + 1]) break;
        positions.push(mid); positions.sort((a, b) => a - b);
        num = numbersFrom(path, positions);
      }
      if (countSolutions(n, num, positions.length, 2, adj) !== 1) continue;

      // Thin out: drop interior checkpoints not needed for uniqueness (the
      // connectivity-pruned solver is fast enough to do this cheaply now).
      const interior = shuffle(positions.filter((p) => p !== 0 && p !== total - 1), rng);
      for (const p of interior) {
        const trial = positions.filter((x) => x !== p);
        if (countSolutions(n, numbersFrom(path, trial), trial.length, 2, adj) === 1) positions = trial;
      }
      num = numbersFrom(path, positions);

      return { size: n, path: path, num: num, k: positions.length };
    }
    return null;
  }

  function dailySeed(date) {
    const d = date || new Date();
    return d.getUTCFullYear() * 10000 + (d.getUTCMonth() + 1) * 100 + d.getUTCDate();
  }

  window.Zip = window.Zip || {};
  window.Zip.generate = generate;
  window.Zip.dailySeed = dailySeed;
})();
