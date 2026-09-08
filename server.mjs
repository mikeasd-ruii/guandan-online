// server/main.ts
import { createServer } from "node:http";
import { readFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";
import { networkInterfaces } from "node:os";

// server/rooms.ts
import { randomBytes, randomUUID, randomInt } from "node:crypto";

// lib/game.ts
var RANKS = Array.from({ length: 13 }, (_, i) => i + 2);
var LABELS = { single: "\u5355\u5F20", pair: "\u5BF9\u5B50", triple: "\u4E09\u5F20", fullhouse: "\u4E09\u5E26\u4E8C", straight: "\u987A\u5B50", pairs: "\u4E09\u8FDE\u5BF9", triples: "\u94A2\u677F", bomb: "\u70B8\u5F39", flush: "\u540C\u82B1\u987A", kings: "\u56DB\u5927\u5929\u738B" };
var rankName = (rank) => ({ 11: "J", 12: "Q", 13: "K", 14: "A", 16: "\u5C0F\u738B", 17: "\u5927\u738B" })[rank] ?? String(rank);
var isWild = (card, level = 2) => card.suit === "H" && card.rank === level;
var strength = (rank, level = 2) => rank === level ? 15 : rank;
var sortCards = (cards, level = 2) => [...cards].sort((a, b) => strength(b.rank, level) - strength(a.rank, level) || Number(isWild(b, level)) - Number(isWild(a, level)) || a.suit.localeCompare(b.suit) || a.id.localeCompare(b.id));
function createDeck() {
  return [0, 1].flatMap((d) => [...RANKS.flatMap((rank) => ["S", "H", "C", "D"].map((suit) => ({ id: `${d}-${suit}-${rank}`, suit, rank }))), { id: `${d}-J-16`, suit: "J", rank: 16 }, { id: `${d}-J-17`, suit: "J", rank: 17 }]);
}
var cache = /* @__PURE__ */ new Map();
function templates(level) {
  if (cache.has(level)) return cache.get(level);
  const result = [];
  const add = (type, needs, power, band = 0, suit) => {
    const size = needs.reduce((n, r) => n + r[1], 0);
    result.push({ type, needs, power, band, size, suit, key: `${type}-${power}-${size}-${suit ?? ""}-${needs.map((n) => n.join(":")).join(",")}`, label: type === "bomb" ? `${size} \u5F20\u70B8\u5F39` : LABELS[type] });
  };
  for (const rank of [...RANKS, 16, 17]) {
    add("pair", [[rank, 2]], strength(rank, level));
    if (rank > 14) continue;
    add("triple", [[rank, 3]], strength(rank, level));
    for (let n = 4; n <= 10; n++) add("bomb", [[rank, n]], strength(rank, level), n);
    for (const other of [...RANKS, 16, 17]) if (other !== rank) add("fullhouse", [[rank, 3], [other, 2]], strength(rank, level));
  }
  for (const [type, length, count] of [["straight", 5, 1], ["pairs", 3, 2], ["triples", 2, 3]]) {
    for (let start = 1; start <= 15 - length; start++) {
      const needs = Array.from({ length }, (_, i) => [start + i === 1 ? 14 : start + i, count]);
      add(type, needs, start + length - 1);
      if (type === "straight") for (const suit of ["S", "H", "C", "D"]) add("flush", needs, start + length - 1, 5.5, suit);
    }
  }
  add("kings", [[16, 2], [17, 2]], 17, 100);
  cache.set(level, result);
  return result;
}
function fill(template, cards, level) {
  const wild = cards.filter((c) => isWild(c, level));
  const natural = cards.filter((c) => !isWild(c, level));
  const output = [];
  let used = 0;
  for (const [rank, count] of template.needs) {
    const group = natural.filter((c) => c.rank === rank && (!template.suit || c.suit === template.suit)).slice(0, count);
    const gap = count - group.length;
    if (gap && (rank > 14 || used + gap > wild.length)) return null;
    output.push(...group, ...wild.slice(used, used + gap));
    used += gap;
  }
  return output;
}
function toHand(t, cards) {
  return { key: t.key, type: t.type, label: t.label, size: t.size, power: t.power, band: t.band, cards };
}
function classify(cards, level = 2) {
  if (!cards.length || new Set(cards.map((c) => c.id)).size !== cards.length) return [];
  if (cards.length === 1) return [{ key: "single", type: "single", label: "\u5355\u5F20", cards, size: 1, power: strength(cards[0].rank, level), band: 0 }];
  return templates(level).filter((t) => t.size === cards.length).flatMap((t) => {
    const found = fill(t, cards, level);
    return found ? [toHand(t, found)] : [];
  }).sort((a, b) => b.band - a.band || b.power - a.power);
}
function beats(hand, target) {
  if (!target) return true;
  if (hand.band !== target.band) return hand.band > target.band;
  if (hand.band > 0) return hand.power > target.power;
  return hand.type === target.type && hand.size === target.size && hand.power > target.power;
}
function legalMoves(cards, target = null, level = 2) {
  const moves = cards.flatMap((c) => classify([c], level)).filter((h) => beats(h, target));
  const flushes = templates(level).filter((t) => t.type === "flush").flatMap((t) => {
    const found = fill(t, cards, level);
    return found ? [found] : [];
  });
  const protectedIds = new Set(flushes.flat().map((c) => c.id));
  const preserve = [...cards].sort((a, b) => Number(protectedIds.has(a.id)) - Number(protectedIds.has(b.id)));
  for (const t of templates(level)) {
    if (t.size > cards.length) continue;
    const prospect = toHand(t, []);
    if (!beats(prospect, target)) continue;
    for (const pool of [cards, preserve]) {
      const found = fill(t, pool, level);
      if (found) moves.push(toHand(t, found));
    }
  }
  const seen = /* @__PURE__ */ new Set();
  return moves.filter((h) => {
    const key = h.cards.map((c) => c.id).sort().join("|") + h.type + h.power;
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}
function newGame(seed = Date.now(), level = 2, round = 1) {
  let value = seed >>> 0;
  const random = () => {
    value = value + 1831565813 | 0;
    let t = Math.imul(value ^ value >>> 15, 1 | value);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
  const deck = createDeck();
  for (let i = deck.length - 1; i > 0; i--) {
    const j = Math.floor(random() * (i + 1));
    [deck[i], deck[j]] = [deck[j], deck[i]];
  }
  return { hands: [0, 1, 2, 3].map((p) => sortCards(deck.slice(p * 27, (p + 1) * 27), level)), level, round, turn: 0, target: null, leader: 0, passes: 0, finished: [], over: false, winner: null, played: [], views: [null, null, null, null], log: [], moves: 0 };
}
function nextActive(state, from) {
  for (let n = 1; n <= 4; n++) {
    const p = (from + n) % 4;
    if (state.hands[p].length) return p;
  }
  return from;
}
function playTurn(state, ids, interpretation) {
  if (state.over) throw new Error("\u672C\u5C40\u5DF2\u7ED3\u675F\uFF0C\u91CD\u65B0\u53D1\u724C\u518D\u6765\u4E00\u5C40\u3002");
  const player = state.turn;
  if (new Set(ids).size !== ids.length) throw new Error("\u540C\u4E00\u5F20\u724C\u53EA\u80FD\u51FA\u4E00\u6B21\u3002");
  const cards = ids.map((id) => state.hands[player].find((c) => c.id === id));
  if (cards.some((c) => !c)) throw new Error("\u53EA\u80FD\u6253\u51FA\u81EA\u5DF1\u7684\u624B\u724C\u3002");
  const s = { ...state, hands: state.hands.map((h) => [...h]), finished: [...state.finished], played: [...state.played], views: [...state.views], log: [...state.log], moves: state.moves + 1 };
  if (!ids.length) {
    if (!s.target) throw new Error("\u73B0\u5728\u7531\u4F60\u9886\u51FA\uFF0C\u81F3\u5C11\u9009\u4E00\u5F20\u724C\u3002");
    s.passes++;
    s.views[player] = { cards: [], label: "\u4E0D\u51FA", pass: true };
    s.log.push({ player, text: "\u4E0D\u51FA", cards: [] });
    const needed = s.hands.filter((h, i) => h.length > 0 && i !== s.leader).length;
    if (s.passes >= needed) {
      const leader = s.hands[s.leader].length ? s.leader : (s.leader + 2) % 4;
      s.turn = s.hands[leader].length ? leader : nextActive(s, leader);
      s.target = null;
      s.passes = 0;
      s.views = [null, null, null, null];
    } else s.turn = nextActive(s, player);
    return s;
  }
  const options = classify(cards, s.level).filter((h) => beats(h, s.target));
  const chosen = interpretation ? options.find((h) => h.key === interpretation) : options[0];
  if (!chosen) throw new Error(options.length ? "\u8BF7\u9009\u62E9\u4E00\u4E2A\u6709\u6548\u7684\u724C\u578B\u89E3\u91CA\u3002" : classify(cards, s.level).length ? "\u8FD9\u624B\u8FD8\u538B\u4E0D\u4F4F\uFF0C\u8BF7\u51FA\u540C\u724C\u578B\u66F4\u5927\u7684\u724C\uFF0C\u6216\u7528\u70B8\u5F39\u3002" : "\u8FD9\u4E9B\u724C\u6682\u65F6\u7EC4\u4E0D\u6210\u724C\u578B\u3002\u53EF\u4EE5\u8BD5\u8BD5\u5BF9\u5B50\uFF0C\u6216\u70B9\u300C\u63D0\u793A\u300D\u3002");
  s.hands[player] = s.hands[player].filter((c) => !ids.includes(c.id));
  s.played.push(...chosen.cards);
  s.target = chosen;
  s.leader = player;
  s.passes = 0;
  s.views[player] = { cards: chosen.cards, label: chosen.label, pass: false };
  s.log.push({ player, text: chosen.label, cards: chosen.cards });
  if (!s.hands[player].length) s.finished.push(player);
  if (s.finished.length >= 3 || s.finished.length === 2 && s.finished[0] % 2 === s.finished[1] % 2) {
    s.over = true;
    s.winner = s.finished[0] % 2;
    if (s.finished.length === 3) s.finished.push([0, 1, 2, 3].find((p) => !s.finished.includes(p)));
  }
  s.turn = nextActive(s, player);
  return s;
}
function suggestMove(s) {
  if (s.over) return null;
  const own = s.hands[s.turn];
  const moves = legalMoves(own, s.target, s.level);
  if (!moves.length) return null;
  const finish = moves.find((m) => m.size === own.length);
  if (finish) return finish;
  const teammateLeads = s.target && s.leader % 2 === s.turn % 2;
  if (teammateLeads) return null;
  const opponents = s.hands.filter((_, p) => p % 2 !== s.turn % 2).map((h) => h.length).filter(Boolean);
  const danger = opponents.some((n) => n <= 2);
  const flushes = legalMoves(own, null, s.level).filter((m) => m.type === "flush");
  const score = (move) => {
    let score2 = move.band * 20 + move.power * 0.65 + move.cards.filter((c) => isWild(c, s.level)).length * 8;
    if (!s.target) score2 -= move.size * 5;
    const ranks = new Set(move.cards.map((c) => c.rank));
    for (const rank of ranks) {
      const all = own.filter((c) => c.rank === rank).length;
      const used = move.cards.filter((c) => c.rank === rank).length;
      if (all >= 4 && used < all) score2 += 25;
      else if (all >= 2 && used === 1) score2 += 6;
    }
    for (const flush of flushes) {
      const used = flush.cards.filter((c) => move.cards.some((m) => m.id === c.id)).length;
      if (used > 0 && used < 5) score2 += 35;
    }
    if (danger && move.type === "single" && !s.target) score2 += 35;
    return score2;
  };
  moves.sort((a, b) => score(a) - score(b));
  if (s.target && moves[0].band > 0 && !danger && own.length > 8 && s.target.power < 14) return null;
  return moves[0];
}

// lib/match.ts
function newMatch(seed = Date.now(), options = {}) {
  return {
    game: newGame(seed),
    levels: [2, 2],
    activeTeam: 0,
    aFailures: [0, 0],
    phase: "play",
    transfers: [],
    firstLeader: 0,
    history: [],
    champion: null,
    notice: "\u4ECE 2 \u6253\u5230 A\uFF0C\u548C\u961F\u53CB\u4E00\u8D77\u8FC7\u5173\u3002",
    options: { aReset: true, difficulty: "normal", ...options }
  };
}
function settleRound(source) {
  const m = structuredClone(source);
  if (!m.game.over) throw new Error("\u8FD9\u526F\u724C\u8FD8\u6CA1\u6709\u7ED3\u675F\u3002");
  if (m.history.some((h) => h.round === m.game.round)) return m;
  const order = m.game.finished;
  const winner = order[0] % 2;
  const partner = (order[0] + 2) % 4;
  const place = order.indexOf(partner) + 1;
  const double = order.length === 2;
  const gain = place === 2 ? 3 : place === 3 ? 2 : 1;
  const passedA = m.game.level === 14 && m.levels[winner] === 14 && place > 0 && place <= 3;
  if (passedA) {
    m.champion = winner;
    m.phase = "complete";
    m.notice = `${winner === 0 ? "\u5357\u5317" : "\u4E1C\u897F"}\u961F\u6210\u529F\u8FC7 A\uFF0C\u8D62\u5F97\u6574\u573A\u6BD4\u8D5B\uFF01`;
  } else {
    if (m.game.level === 14 && m.levels[m.activeTeam] === 14) {
      m.aFailures[m.activeTeam]++;
      if (m.options.aReset && m.aFailures[m.activeTeam] >= 3) {
        m.levels[m.activeTeam] = 2;
        m.aFailures[m.activeTeam] = 0;
      }
    }
    if (!(m.game.level === 14 && source.levels[winner] === 14))
      m.levels[winner] = Math.min(14, m.levels[winner] + gain);
    m.phase = "between";
    m.notice = `${winner === 0 ? "\u5357\u5317" : "\u4E1C\u897F"}\u961F${double ? "\u53CC\u4E0A" : ""}\u83B7\u80DC\uFF0C\u4E0B\u526F\u6253 ${rankName(m.levels[winner])}\u3002`;
  }
  m.history.push({
    round: m.game.round,
    level: m.game.level,
    winner,
    order: [...order],
    double,
    gain,
    message: m.notice
  });
  return m;
}
function prepareTribute(source, dealt) {
  const m = structuredClone(source);
  const previous = m.history.at(-1);
  if (!previous) throw new Error("\u6CA1\u6709\u4E0A\u4E00\u526F\u724C\u7684\u7ED3\u679C\u3002");
  m.game = dealt;
  m.phase = "tribute";
  m.transfers = [];
  m.champion = null;
  m.activeTeam = previous.winner;
  const head = previous.order[0];
  const donors = previous.double ? [0, 1, 2, 3].filter((p) => !previous.order.includes(p)) : [previous.order[3]];
  const redKings = donors.flatMap((p) => m.game.hands[p]).filter((c) => c.rank === 17).length;
  if (redKings === 2) {
    m.phase = "play";
    m.firstLeader = head;
    m.game.turn = head;
    m.notice = "\u4E24\u5F20\u5927\u738B\uFF0C\u6297\u8D21\u6210\u529F\u3002\u672C\u526F\u514D\u8D21\u514D\u8FD8\uFF0C\u7531\u4E0A\u526F\u5934\u6E38\u5148\u51FA\u3002";
    return m;
  }
  m.transfers = donors.map((from) => ({
    from,
    to: head,
    gift: null,
    back: null
  }));
  m.firstLeader = donors[0];
  m.notice = previous.double ? "\u53CC\u4E0B\u65B9\u5404\u8FDB\u8D21\u4E00\u5F20\u6700\u5927\u724C\u3002\u4E24\u5F20\u8D21\u724C\u9009\u597D\u540E\uFF0C\u518D\u51B3\u5B9A\u6D41\u5411\u3002" : "\u672B\u6E38\u5411\u5934\u6E38\u8FDB\u8D21\u6700\u5927\u724C\uFF0C\u7EA2\u6843\u7EA7\u724C\u4E0D\u8FDB\u8D21\u3002";
  return m;
}
function beginNextRound(source, seed = Date.now()) {
  if (source.phase !== "between") throw new Error("\u8BF7\u5148\u6253\u5B8C\u672C\u526F\u724C\u3002");
  const winner = source.history.at(-1).winner;
  return prepareTribute(
    source,
    newGame(seed, source.levels[winner], source.game.round + 1)
  );
}
function actor(m) {
  return m.phase === "play" ? m.game.turn : m.phase === "tribute" ? m.transfers.find((t) => !t.gift)?.from ?? null : m.phase === "return" ? m.transfers.find((t) => !t.back)?.to ?? null : null;
}
function eligibleCards(m, seat) {
  if (actor(m) !== seat) return [];
  const hand = m.game.hands[seat];
  const level = m.game.level;
  if (m.phase === "tribute") {
    const available = hand.filter((c) => !isWild(c, level));
    const max = Math.max(...available.map((c) => strength(c.rank, level)));
    return available.filter((c) => strength(c.rank, level) === max);
  }
  if (m.phase === "return") {
    const low = hand.filter((c) => strength(c.rank, level) <= 10);
    if (low.length) return low;
    const min = Math.min(...hand.map((c) => strength(c.rank, level)));
    return hand.filter((c) => strength(c.rank, level) === min);
  }
  return [];
}
function matchAction(source, seat, action) {
  if (actor(source) !== seat) throw new Error("\u8FD8\u6CA1\u8F6E\u5230\u4F60\uFF0C\u8BF7\u7B49\u5F85\u5F53\u524D\u73A9\u5BB6\u3002");
  if (action.type === "play") {
    if (source.phase !== "play") throw new Error("\u5148\u5B8C\u6210\u8FDB\u8D21\u548C\u8FD8\u8D21\u3002");
    const m2 = {
      ...source,
      game: playTurn(source.game, action.ids, action.key)
    };
    return m2.game.over ? settleRound(m2) : m2;
  }
  if (action.type !== source.phase) throw new Error("\u8FD9\u9879\u64CD\u4F5C\u4E0D\u5C5E\u4E8E\u5F53\u524D\u9636\u6BB5\u3002");
  if (!eligibleCards(source, seat).some((c) => c.id === action.cardId))
    throw new Error(
      source.phase === "tribute" ? "\u8BF7\u9009\u6700\u5927\u724C\uFF0C\u7EA2\u6843\u7EA7\u724C\u4E0D\u8FDB\u8D21\u3002" : "\u8BF7\u9009\u62E9\u4E0D\u5927\u4E8E 10 \u7684\u975E\u7EA7\u724C\uFF1B\u6CA1\u6709\u65F6\u9009\u6700\u5C0F\u724C\u3002"
    );
  const m = structuredClone(source);
  const card = m.game.hands[seat].find((c) => c.id === action.cardId);
  if (action.type === "tribute") {
    m.transfers.find((t) => t.from === seat).gift = card;
    if (m.transfers.every((t) => t.gift)) {
      const head = m.history.at(-1).order[0];
      m.transfers.sort(
        (a, b) => strength(b.gift.rank, m.game.level) - strength(a.gift.rank, m.game.level) || Number(b.from === (head + 1) % 4) - Number(a.from === (head + 1) % 4)
      );
      m.transfers.forEach((t, i) => {
        t.to = i === 0 ? head : (head + 2) % 4;
      });
      m.firstLeader = m.transfers[0].from;
      for (const t of m.transfers)
        m.game.hands[t.from] = m.game.hands[t.from].filter(
          (c) => c.id !== t.gift.id
        );
      for (const t of m.transfers) m.game.hands[t.to].push(t.gift);
      m.phase = "return";
      m.notice = "\u6536\u5230\u8D21\u724C\u540E\uFF0C\u5404\u8FD8\u4E00\u5F20\u4E0D\u5927\u4E8E 10 \u7684\u975E\u7EA7\u724C\u3002\u6CA1\u6709\u5408\u9002\u5C0F\u724C\u65F6\u8FD8\u6700\u5C0F\u724C\u3002";
    }
  } else {
    m.transfers.find((t) => t.to === seat).back = card;
    if (m.transfers.every((t) => t.back)) {
      for (const t of m.transfers)
        m.game.hands[t.to] = m.game.hands[t.to].filter(
          (c) => c.id !== t.back.id
        );
      for (const t of m.transfers) m.game.hands[t.from].push(t.back);
      m.phase = "play";
      m.game.turn = m.firstLeader;
      m.notice = "\u8FDB\u8D21\u3001\u8FD8\u8D21\u5B8C\u6210\u3002\u5411\u5934\u6E38\u8FDB\u8D21\u7684\u73A9\u5BB6\u5148\u51FA\u3002";
    }
  }
  m.game.hands = m.game.hands.map((h) => sortCards(h, m.game.level));
  return m;
}
function publicMatch(m, seat) {
  const { hands, ...game } = m.game;
  return {
    ...m,
    game: { ...game, hand: hands[seat], counts: hands.map((h) => h.length) },
    transfers: m.transfers.map((t) => ({
      ...t,
      gift: m.phase === "tribute" && t.from !== seat ? null : t.gift,
      back: m.phase === "return" && t.to !== seat ? null : t.back
    })),
    eligible: eligibleCards(m, seat).map((c) => c.id),
    actor: actor(m)
  };
}

// lib/ai.ts
var popcount = (n) => {
  let c = 0;
  while (n) {
    n &= n - 1;
    c++;
  }
  return c;
};
function partitionSolver(s, deep) {
  const hand = s.hands[s.turn];
  const index = new Map(hand.map((c, i) => [c.id, i]));
  const maskOf = (h) => h.cards.reduce((mask, c) => mask | 1 << index.get(c.id), 0);
  const groups = /* @__PURE__ */ new Set();
  for (const pool of [hand, [...hand.slice(1), hand[0]]])
    for (const h of legalMoves(pool, null, s.level)) groups.add(maskOf(h));
  const masks = [...groups].sort((a, b) => popcount(b) - popcount(a));
  const buckets = hand.map((_, i) => masks.filter((m) => (m & 1 << i) !== 0));
  const memo = /* @__PURE__ */ new Map([[0, 0]]);
  let budget = deep ? hand.length <= 12 ? 18e3 : 3200 : 850;
  const greedy = (mask) => {
    let count = 0;
    for (const m of masks)
      if ((mask & m) === m) {
        mask ^= m;
        count++;
        if (!mask) break;
      }
    return count + popcount(mask);
  };
  const solve = (mask) => {
    const cached = memo.get(mask);
    if (cached !== void 0) return cached;
    let best = greedy(mask);
    if (best <= 1 || budget-- <= 0) return best;
    const bit = 31 - Math.clz32(mask & -mask);
    for (const group of buckets[bit]) {
      if ((mask & group) !== group) continue;
      const left = mask ^ group;
      if (!left) {
        best = 1;
        break;
      }
      const lower = Math.ceil(popcount(left) / 10) + 1;
      if (lower >= best) continue;
      best = Math.min(best, 1 + solve(left));
      if (best <= 2) break;
    }
    memo.set(mask, best);
    return best;
  };
  return {
    remaining: (h) => solve((1 << hand.length) - 1 ^ maskOf(h))
  };
}
function biggerRisk(s, h, unknown) {
  if (h.band || !["single", "pair", "triple"].includes(h.type)) return 0.3;
  const needed = h.size;
  const eligible = unknown.filter((c) => strength(c.rank, s.level) > h.power);
  if (!eligible.length) return 0;
  const opponents = s.hands.filter((_, p) => p % 2 !== s.turn % 2).map((x) => x.length).filter(Boolean);
  if (needed === 1) {
    let risk2 = 0;
    for (const count of opponents) {
      let no = 1;
      for (let i = 0; i < count; i++)
        no *= Math.max(0, unknown.length - eligible.length - i) / (unknown.length - i);
      risk2 = Math.max(risk2, 1 - no);
    }
    return risk2;
  }
  const wilds = unknown.filter((c) => isWild(c, s.level)).length;
  const combinations = (n, k) => {
    if (n < k) return 0;
    let result = 1;
    for (let i = 1; i <= k; i++) result = result * (n - i + 1) / i;
    return result;
  };
  let risk = 0;
  for (const rank of [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17]) {
    if (strength(rank, s.level) <= h.power) continue;
    const natural = unknown.filter(
      (c) => c.rank === rank && !isWild(c, s.level)
    ).length;
    const total = natural + (rank <= 14 ? wilds : 0);
    if (total < needed) continue;
    for (const count of opponents) {
      let probability = 1;
      for (let i = 0; i < needed; i++)
        probability *= Math.max(0, count - i) / Math.max(1, unknown.length - i);
      risk += probability * combinations(total, needed);
    }
  }
  return Math.min(1, risk);
}
function chooseMove(s, difficulty = "normal") {
  if (s.over) return null;
  if (difficulty === "normal") return suggestMove(s);
  const own = s.hands[s.turn];
  const moves = legalMoves(own, s.target, s.level);
  if (!moves.length) return null;
  const finish = moves.find((h) => h.size === own.length);
  if (finish) return finish;
  if (difficulty === "easy") {
    if (s.target && s.leader % 2 === s.turn % 2) return null;
    return moves.sort(
      (a, b) => a.band - b.band || a.power - b.power || b.size - a.size
    )[0];
  }
  const unknown = createDeck().filter(
    (c) => !own.some((o) => o.id === c.id) && !s.played.some((p) => p.id === c.id)
  );
  const enemies = s.hands.filter((_, p) => p % 2 !== s.turn % 2).map((h) => h.length).filter(Boolean);
  const imminent = enemies.some((n) => n <= 2);
  if (s.target && s.leader % 2 === s.turn % 2) {
    if (s.target.type === "single" && enemies.includes(1) && own.length <= 6) {
      const cover = moves.filter((h) => h.type === "single" && biggerRisk(s, h, unknown) === 0).sort((a, b) => b.power - a.power)[0];
      if (cover) return cover;
    }
    return null;
  }
  const solver = partitionSolver(s, difficulty === "master");
  const naturalBombs = legalMoves(own, null, s.level).filter(
    (h) => h.band >= 4
  );
  const score = (h) => {
    const left = solver.remaining(h);
    let value = left * 70 + h.power * 0.35 - h.size * 0.4;
    value += h.cards.filter((c) => isWild(c, s.level)).length * 3;
    if (h.band) {
      const canExit = left <= 1 && enemies.every((n) => n < 4);
      value += canExit ? -65 : imminent ? 5 : 24;
    } else
      for (const bomb of naturalBombs) {
        const taken = bomb.cards.filter(
          (c) => h.cards.some((x) => x.id === c.id)
        ).length;
        if (taken && taken < bomb.size) value += 12;
      }
    const risk = biggerRisk(s, h, unknown);
    if (imminent && s.target?.type === "single" && h.type === "single")
      value += risk * 70 - h.power * 2;
    if (!s.target && enemies.includes(1) && h.type === "single")
      value += risk * 105;
    if (!s.target && enemies.includes(2) && h.type === "pair")
      value += risk * 65;
    if (left === 1) value += risk * 22;
    return value;
  };
  const ranked = moves.map((h) => ({ h, value: score(h) })).sort((a, b) => a.value - b.value || a.h.power - b.h.power);
  const best = ranked[0].h;
  if (s.target && best.band && solver.remaining(best) > 1 && enemies.every((n) => n > 3) && own.length > 8)
    return null;
  return best;
}

// server/rooms.ts
var cleanName = (value) => {
  if (typeof value !== "string" || !value.trim())
    throw new Error("\u5148\u586B\u4E00\u4E2A\u6635\u79F0\u3002");
  return value.trim().split("").filter((char) => char.charCodeAt(0) >= 32).join("").slice(0, 12);
};
var RoomService = class {
  constructor(clock = Date.now) {
    this.rooms = /* @__PURE__ */ new Map();
    this.clock = clock;
  }
  create(name, options = {}) {
    this.tick();
    if (this.rooms.size >= 32) throw new Error("\u724C\u684C\u6682\u65F6\u5DF2\u6EE1\uFF0C\u7A0D\u540E\u518D\u8BD5\u3002");
    const id = randomBytes(5).toString("hex").slice(0, 8).toUpperCase();
    const token = randomBytes(32).toString("hex");
    const room = {
      id,
      instance: randomUUID(),
      members: [
        { name: cleanName(name), token, seen: this.clock() },
        null,
        null,
        null
      ],
      owner: 0,
      match: null,
      revision: 0,
      nextMoveAt: 0,
      active: this.clock(),
      options: {
        aReset: options.aReset !== false,
        difficulty: this.validDifficulty(options.difficulty ?? "hard")
      },
      seenActions: /* @__PURE__ */ new Set()
    };
    this.rooms.set(id, room);
    return { roomId: id, token, seat: 0 };
  }
  validDifficulty(d) {
    if (!["easy", "normal", "hard", "master"].includes(String(d)))
      throw new Error("\u96BE\u5EA6\u65E0\u6548\u3002");
    return d;
  }
  room(id) {
    const r = this.rooms.get(String(id).toUpperCase());
    if (!r) throw new Error("\u623F\u95F4\u4E0D\u5B58\u5728\u6216\u5DF2\u7ED3\u675F\uFF0C\u8BF7\u91CD\u65B0\u5F00\u623F\u3002");
    return r;
  }
  authenticate(id, token) {
    const room = this.room(id);
    const seat = room.members.findIndex((m) => m?.token === token);
    if (seat < 0) throw new Error("\u52A0\u5165\u51ED\u8BC1\u5DF2\u5931\u6548\uFF0C\u8BF7\u91CD\u65B0\u52A0\u5165\u623F\u95F4\u3002");
    const member = room.members[seat];
    member.seen = this.clock();
    room.active = this.clock();
    return { room, seat };
  }
  join(id, name, wanted) {
    const room = this.room(id);
    if (room.match && room.match.phase !== "between" && room.match.phase !== "complete")
      throw new Error("\u5DF2\u5F00\u5C40\uFF0C\u8BF7\u7B49\u5230\u4E00\u526F\u7ED3\u675F\u540E\u518D\u52A0\u5165\u3002");
    let seat = room.members.findIndex((m) => m === null);
    if (wanted !== void 0) {
      if (!Number.isInteger(wanted) || wanted < 0 || wanted > 3)
        throw new Error("\u5EA7\u4F4D\u65E0\u6548\u3002");
      if (room.members[wanted]) throw new Error("\u8FD9\u4E2A\u5EA7\u4F4D\u6709\u4EBA\u4E86\u3002");
      seat = wanted;
    }
    if (seat < 0) throw new Error("\u623F\u95F4\u5DF2\u7ECF\u5750\u6EE1 4 \u4EBA\u3002");
    const token = randomBytes(32).toString("hex");
    room.members[seat] = { name: cleanName(name), token, seen: this.clock() };
    room.revision++;
    room.active = this.clock();
    return { roomId: room.id, token, seat };
  }
  snapshot(room, seat) {
    const now = this.clock();
    const online = room.members.map((m) => !!m && now - m.seen < 2e4);
    if (!online[room.owner]) {
      const next = online.findIndex(Boolean);
      if (next >= 0 && next !== room.owner) {
        room.owner = next;
        room.revision++;
      }
    }
    return {
      roomId: room.id,
      instance: room.instance,
      revision: room.revision,
      you: seat,
      owner: room.owner,
      members: room.members.map((m, p) => ({
        seat: p,
        name: m?.name ?? ["\u5357\u98CE", "\u4E1C\u98CE", "\u5317\u98CE", "\u897F\u98CE"][p],
        human: !!m,
        online: online[p],
        autoplay: !m || now - m.seen >= 25e3
      })),
      match: room.match ? publicMatch(room.match, seat) : null,
      options: room.options
    };
  }
  state(id, token) {
    const { room, seat } = this.authenticate(id, token);
    return this.snapshot(room, seat);
  }
  command(id, token, command, revision, actionId) {
    const { room, seat } = this.authenticate(id, token);
    if (typeof actionId !== "string" || actionId.length < 1 || actionId.length > 100)
      throw new Error("\u64CD\u4F5C\u7F16\u53F7\u65E0\u6548\u3002");
    const dedup = token + ":" + actionId;
    if (room.seenActions.has(dedup)) return this.snapshot(room, seat);
    if (revision !== room.revision)
      throw new Error("\u724C\u5C40\u521A\u66F4\u65B0\uFF0C\u8BF7\u770B\u6700\u65B0\u724C\u9762\u518D\u64CD\u4F5C\u3002");
    if (!command || typeof command !== "object") throw new Error("\u64CD\u4F5C\u65E0\u6548\u3002");
    const owner = () => {
      this.snapshot(room, seat);
      if (room.owner !== seat) throw new Error("\u8BF7\u7531\u623F\u4E3B\u64CD\u4F5C\u3002");
    };
    if (command.type === "start") {
      owner();
      if (room.match) throw new Error("\u8FD9\u573A\u724C\u5DF2\u7ECF\u5F00\u59CB\u4E86\u3002");
      room.match = newMatch(randomInt(0, 4294967295), room.options);
    } else if (command.type === "next") {
      owner();
      if (!room.match) throw new Error("\u8FD8\u6CA1\u6709\u5F00\u59CB\u3002");
      room.match = beginNextRound(room.match, randomInt(0, 4294967295));
    } else if (command.type === "restart") {
      owner();
      room.match = newMatch(randomInt(0, 4294967295), room.options);
    } else if (command.type === "options") {
      owner();
      if (room.match) throw new Error("\u5F00\u5C40\u540E\u4E0D\u80FD\u4FEE\u6539\u623F\u95F4\u89C4\u5219\u3002");
      room.options = {
        difficulty: this.validDifficulty(command.difficulty),
        aReset: command.aReset !== false
      };
    } else if (command.type === "seat") {
      if (room.match) throw new Error("\u5F00\u5C40\u540E\u4E0D\u80FD\u6362\u5EA7\u3002");
      const to = command.seat;
      if (!Number.isInteger(to) || to < 0 || to > 3 || room.members[to])
        throw new Error("\u8FD9\u4E2A\u5EA7\u4F4D\u4E0D\u80FD\u9009\u62E9\u3002");
      room.members[to] = room.members[seat];
      room.members[seat] = null;
      if (room.owner === seat) room.owner = to;
      room.revision++;
      room.seenActions.add(dedup);
      return this.snapshot(room, to);
    } else {
      if (!room.match) throw new Error("\u8BF7\u5148\u5F00\u59CB\u5BF9\u5C40\u3002");
      if (!["play", "tribute", "return"].includes(command.type))
        throw new Error("\u672A\u77E5\u64CD\u4F5C\u3002");
      room.match = matchAction(room.match, seat, command);
    }
    room.revision++;
    room.nextMoveAt = this.clock() + 950;
    room.seenActions.add(dedup);
    if (room.seenActions.size > 1500)
      room.seenActions.delete(room.seenActions.values().next().value);
    return this.snapshot(room, seat);
  }
  leave(id, token) {
    const { room, seat } = this.authenticate(id, token);
    room.members[seat] = null;
    room.revision++;
    if (room.members.every((m) => !m)) this.rooms.delete(room.id);
    return { left: true };
  }
  tick() {
    const now = this.clock();
    for (const room of this.rooms.values()) {
      if (now - room.active > 15 * 60 * 1e3) {
        this.rooms.delete(room.id);
        continue;
      }
      const match = room.match;
      if (!match || now < room.nextMoveAt) continue;
      const turn = actor(match);
      if (turn === null) continue;
      const member = room.members[turn];
      if (member && now - member.seen < 25e3) continue;
      if (match.phase === "play") {
        const move = chooseMove(match.game, match.options.difficulty);
        room.match = matchAction(match, turn, {
          type: "play",
          ids: move?.cards.map((c) => c.id) ?? [],
          key: move?.key
        });
      } else {
        const cards = eligibleCards(match, turn);
        room.match = matchAction(match, turn, {
          type: match.phase,
          cardId: cards.at(-1).id
        });
      }
      room.revision++;
      room.nextMoveAt = now + 950;
    }
  }
};

// server/main.ts
function createGameServer({
  htmlPath = resolve(dirname(fileURLToPath(import.meta.url)), "\u63BC\u86CB\u5C0F\u9986.html"),
  rooms = new RoomService()
} = {}) {
  const limits = /* @__PURE__ */ new Map();
  const server = createServer(async (req, res) => {
    res.setHeader("Access-Control-Allow-Origin", "*");
    res.setHeader(
      "Access-Control-Allow-Headers",
      "Content-Type, Authorization"
    );
    res.setHeader("Access-Control-Allow-Methods", "GET, POST, OPTIONS");
    res.setHeader("Cache-Control", "no-store");
    res.setHeader("X-Content-Type-Options", "nosniff");
    if (req.method === "OPTIONS") {
      res.writeHead(204);
      res.end();
      return;
    }
    try {
      if (req.method === "GET" && (req.url === "/" || req.url?.startsWith("/?") || req.url === "/index.html")) {
        if (!htmlPath) throw new Error("\u6CA1\u6709\u9875\u9762\u6587\u4EF6\u3002");
        res.setHeader("Content-Type", "text/html; charset=utf-8");
        res.end(await readFile(htmlPath));
        return;
      }
      if (req.method === "GET" && req.url === "/health") {
        res.setHeader("Content-Type", "application/json");
        res.end('{"ok":true,"game":"guandan"}');
        return;
      }
      if (req.method !== "POST" || req.url !== "/api") {
        res.writeHead(404);
        res.end("Not found");
        return;
      }
      const ip = req.socket.remoteAddress ?? "unknown";
      const now = Date.now();
      let limit = limits.get(ip);
      if (!limit || now - limit.time > 6e4) {
        limit = { time: now, requests: 0, creates: 0 };
        limits.set(ip, limit);
      }
      if (++limit.requests > 1e3) throw new Error("\u8BF7\u6C42\u592A\u9891\u7E41\uFF0C\u8BF7\u7A0D\u540E\u518D\u8BD5\u3002");
      const chunks = [];
      let bytes = 0;
      for await (const chunk of req) {
        const buffer = Buffer.from(chunk);
        bytes += buffer.length;
        if (bytes > 12e3) {
          res.writeHead(413);
          res.end('{"error":"\u8BF7\u6C42\u8FC7\u5927"}');
          return;
        }
        chunks.push(buffer);
      }
      const data = JSON.parse(Buffer.concat(chunks).toString("utf8"));
      if (!data || typeof data !== "object" || Array.isArray(data))
        throw new Error("\u8BF7\u6C42\u683C\u5F0F\u65E0\u6548\u3002");
      const token = String(req.headers.authorization ?? "").replace(
        /^Bearer /,
        ""
      );
      let result;
      if (data.op === "create") {
        if (++limit.creates > 12) throw new Error("\u5F00\u623F\u592A\u9891\u7E41\uFF0C\u8BF7\u7A0D\u540E\u518D\u8BD5\u3002");
        result = rooms.create(data.name, data.options);
      } else if (data.op === "join")
        result = rooms.join(data.roomId, data.name, data.seat);
      else if (data.op === "state") result = rooms.state(data.roomId, token);
      else if (data.op === "command")
        result = rooms.command(
          data.roomId,
          token,
          data.command,
          data.revision,
          data.actionId
        );
      else if (data.op === "leave") result = rooms.leave(data.roomId, token);
      else throw new Error("\u672A\u77E5\u8BF7\u6C42\u3002");
      res.setHeader("Content-Type", "application/json; charset=utf-8");
      res.end(JSON.stringify(result));
    } catch (error) {
      res.writeHead(400, { "Content-Type": "application/json; charset=utf-8" });
      res.end(
        JSON.stringify({
          error: error instanceof Error ? error.message : "\u8BF7\u6C42\u5931\u8D25\u3002"
        })
      );
    }
  });
  const interval = setInterval(() => {
    rooms.tick();
    for (const [ip, entry] of limits)
      if (Date.now() - entry.time > 12e4) limits.delete(ip);
  }, 350);
  interval.unref();
  server.on("close", () => clearInterval(interval));
  return server;
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const port = Number(process.env.PORT ?? 7788);
  const server = createGameServer();
  server.listen(port, "0.0.0.0", () => {
    console.log(`\u63BC\u86CB\u5C0F\u9986\u5DF2\u542F\u52A8\uFF1A http://localhost:${port}`);
    for (const list of Object.values(networkInterfaces()))
      for (const address of list ?? [])
        if (address.family === "IPv4" && !address.internal && /^(10\.|192\.168\.|172\.(1[6-9]|2\d|3[01])\.)/.test(address.address))
          console.log(
            `\u540C Wi-Fi \u7684\u624B\u673A\u6253\u5F00\uFF1A http://${address.address}:${port}`
          );
    console.log(
      "\u4FDD\u6301\u6B64\u670D\u52A1\u8FD0\u884C\u3002\u516C\u7F51\u8054\u673A\u8BF7\u90E8\u7F72\u5230\u670D\u52A1\u5668\u5E76\u4F7F\u7528 HTTPS\u3002\u6309 Ctrl+C \u505C\u6B62\u3002"
    );
  });
  server.on("error", (error) => {
    console.error("\u542F\u52A8\u5931\u8D25\uFF1A" + error.message);
    process.exitCode = 1;
  });
}
export {
  createGameServer
};
