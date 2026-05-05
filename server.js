const express = require('express');
const http = require('http');
const { WebSocketServer } = require('ws');
const path = require('path');

// ==================== 游戏常量 ====================
const TILE = 40, MAP_W = 40, MAP_H = 30;
const WORLD_W = MAP_W * TILE, WORLD_H = MAP_H * TILE;
const PLAYER_SPEED = 220, BOT_SPEED = 170;
const BULLET_SPEED = 750, FIRE_INTERVAL = 130;
const RELOAD_TIME = 1000, MAG_SIZE = 5, RESERVE_MAX = 10;
const MAX_HP = 5, CHAR_SIZE = 16, BULLET_R = 3;
const PICKUP_RESPAWN = 15000;
const TICK_RATE = 50; // ms per tick (20 Hz)
const AUTO_AIM_RANGE = 420; // 自动瞄准范围
const MAX_PLAYERS = 5;
const TEAM_SIZE = 5;            // 5v5 每队人数
const TOTAL_SLOTS_5V5 = 10;    // 5v5 总人数
const MODE_DM = 'deathmatch';
const MODE_5V5 = 'team_battle';
const TEAM_BLUE = 'blue';
const TEAM_RED = 'red';
const CRYSTAL_HP = 100;
const CRYSTAL_REGEN_DELAY = 3000;  // 3秒不受击开始回血
const CRYSTAL_REGEN_RATE = 10;     // 每秒回10
const RESPAWN_TIME = 5000;         // 复活5秒
const KILL_HP_BONUS = 2;           // 击杀+2血
const KILL_DMG_BONUS = 1;          // 击杀+1伤害
const MINION_SPAWN_DELAY = 90000;  // 90秒后开始出小兵
const MINION_INTERVAL = 1000;      // 每秒一个
const MINION_HP = 3;
const MINION_DMG = 1;
const MINION_SPEED = 100;
const MINION_ATK_RANGE = 50;
const MINION_ATK_INTERVAL = 500;

// 水晶出生点
const CRYSTAL_POS = {
  blue:  { x: 5 * TILE + TILE/2,  y: 5 * TILE + TILE/2 },
  red:   { x: 34 * TILE + TILE/2, y: 24 * TILE + TILE/2 }
};

// 5v5 双方出生点
const TEAM_SPAWNS = {
  blue: [
    { x: 3*TILE+TILE/2, y: 2*TILE+TILE/2 },
    { x: 6*TILE+TILE/2, y: 2*TILE+TILE/2 },
    { x: 2*TILE+TILE/2, y: 6*TILE+TILE/2 },
    { x: 6*TILE+TILE/2, y: 6*TILE+TILE/2 },
    { x: 4*TILE+TILE/2, y: 4*TILE+TILE/2 },
  ],
  red: [
    { x: 37*TILE+TILE/2, y: 22*TILE+TILE/2 },
    { x: 34*TILE+TILE/2, y: 22*TILE+TILE/2 },
    { x: 37*TILE+TILE/2, y: 26*TILE+TILE/2 },
    { x: 34*TILE+TILE/2, y: 26*TILE+TILE/2 },
    { x: 36*TILE+TILE/2, y: 24*TILE+TILE/2 },
  ]
};

// A* 寻路
function aStarPath(worldStart, worldEnd) {
  const s = { x: Math.floor(worldStart.x/TILE), y: Math.floor(worldStart.y/TILE) };
  const e = { x: Math.floor(worldEnd.x/TILE),   y: Math.floor(worldEnd.y/TILE) };
  const key = (x,y) => x+','+y;
  const h = (x,y) => Math.abs(x-e.x) + Math.abs(y-e.y);
  const open = [{ x:s.x, y:s.y, g:0, f:h(s.x,s.y), parent:null }];
  const closed = new Set();
  closed.add(key(s.x, s.y));
  const dirs = [[0,-1],[1,0],[0,1],[-1,0],[1,-1],[1,1],[-1,1],[-1,-1]];
  while (open.length > 0) {
    let best = 0;
    for (let i = 1; i < open.length; i++) if (open[i].f < open[best].f) best = i;
    const cur = open.splice(best, 1)[0];
    if (cur.x === e.x && cur.y === e.y) {
      const path = []; let node = cur;
      while (node) { path.unshift({ x: node.x*TILE+TILE/2, y: node.y*TILE+TILE/2 }); node = node.parent; }
      return path;
    }
    for (const [dx,dy] of dirs) {
      const nx = cur.x + dx, ny = cur.y + dy;
      if (nx < 0 || nx >= MAP_W || ny < 0 || ny >= MAP_H) continue;
      if (closed.has(key(nx,ny))) continue;
      if (MAP_DATA[ny][nx] === 1) continue;
      // 对角线检查相邻墙
      if (dx !== 0 && dy !== 0) {
        if (MAP_DATA[cur.y+dy] && MAP_DATA[cur.y+dy][cur.x] === 1) continue;
        if (MAP_DATA[cur.y][cur.x+dx] === 1) continue;
      }
      const g = cur.g + (dx !== 0 && dy !== 0 ? 1.414 : 1);
      closed.add(key(nx, ny));
      open.push({ x: nx, y: ny, g, f: g + h(nx, ny), parent: cur });
    }
  }
  return null; // 无路径
}

const CRYSTAL_ATK_RANGE = 480;  // 大于玩家自瞄范围420
const CRYSTAL_ATK_DMG = 3;
const CRYSTAL_ATK_INTERVAL = 500; // ms
const HEAL_RADIUS = 90;
const HEAL_RATE = 8; // 每秒回血

// ==================== 5v5 水晶 ====================
class Crystal {
  constructor(team, x, y, healX, healY) {
    this.team = team;
    this.x = x; this.y = y;
    this.healX = healX; this.healY = healY; // 回血圈中心 (出生点)
    this.hp = CRYSTAL_HP;
    this.maxHp = CRYSTAL_HP;
    this.alive = true;
    this.lastHitTime = 0;
    this.r = 28;
    this.attackCooldown = 0;
  }
  takeDamage(dmg, gameTime) {
    if (!this.alive) return;
    this.hp -= dmg;
    this.lastHitTime = gameTime;
    if (this.hp <= 0) { this.hp = 0; this.alive = false; }
  }
  update(dt, gameTime) {
    if (!this.alive) return;
    if (this.attackCooldown > 0) this.attackCooldown -= dt;
    if (gameTime - this.lastHitTime > CRYSTAL_REGEN_DELAY / 1000) {
      this.hp = Math.min(this.maxHp, this.hp + CRYSTAL_REGEN_RATE * dt);
    }
  }
  findTarget(allPlayers, minions) {
    // 优先小兵
    let best = null, bestDist = CRYSTAL_ATK_RANGE;
    for (const m of minions) {
      if (!m.alive || m.team === this.team) continue;
      const d = Math.hypot(this.x - m.x, this.y - m.y);
      if (d < bestDist) { best = m; bestDist = d; }
    }
    if (best) return best;
    // 其次玩家
    for (const p of allPlayers) {
      if (!p.alive || p.team === this.team) continue;
      const d = Math.hypot(this.x - p.x, this.y - p.y);
      if (d < bestDist) { best = p; bestDist = d; }
    }
    return best;
  }
  tryAttack(target) {
    if (!target || !target.alive || this.attackCooldown > 0) return false;
    this.attackCooldown = CRYSTAL_ATK_INTERVAL / 1000;
    if (typeof target.hp === 'number') {
      target.hp -= CRYSTAL_ATK_DMG;
      if (target.hp <= 0) { target.hp = 0; target.alive = false; }
    }
    return true;
  }
  isInHealZone(px, py) {
    return Math.hypot(px - this.healX, py - this.healY) < HEAL_RADIUS;
  }
  serialize() {
    return { team: this.team, x: this.x, y: this.y, hp: Math.floor(this.hp), maxHp: this.maxHp, alive: this.alive, r: this.r, healX: this.healX, healY: this.healY, healR: HEAL_RADIUS };
  }
}

// ==================== 5v5 小兵 ====================
class Minion {
  constructor(id, team, x, y, targetCrystal, path) {
    this.id = id;
    this.team = team;
    this.x = x; this.y = y;
    this.hp = MINION_HP;
    this.alive = true;
    this.speed = MINION_SPEED;
    this.targetCrystal = targetCrystal; // 敌方水晶
    this.path = path || []; // A* 路径点
    this.pathIndex = 0;
    this.attackCooldown = 0;
    this.attackTarget = null;
    this.attackRange = MINION_ATK_RANGE;
    this.r = 10;
  }
  update(dt, allPlayers, crystals, otherMinions, gameTime) {
    if (!this.alive) return;
    if (this.attackCooldown > 0) this.attackCooldown -= dt;

    // 寻找攻击目标
    this.attackTarget = null;
    let minDist = this.attackRange;
    // 优先攻击敌方水晶
    const enemyCrystal = crystals.find(c => c.team !== this.team && c.alive);
    if (enemyCrystal) {
      const cd = Math.hypot(this.x - enemyCrystal.x, this.y - enemyCrystal.y);
      if (cd < this.attackRange + enemyCrystal.r) { this.attackTarget = enemyCrystal; minDist = cd; }
    }
    // 敌方玩家
    for (const p of allPlayers) {
      if (!p.alive || p.team === this.team) continue;
      const d = Math.hypot(this.x - p.x, this.y - p.y);
      if (d < minDist) { this.attackTarget = p; minDist = d; }
    }
    // 敌方小兵
    for (const m of otherMinions) {
      if (!m.alive || m.team === this.team) continue;
      const d = Math.hypot(this.x - m.x, this.y - m.y);
      if (d < minDist) { this.attackTarget = m; minDist = d; }
    }

    if (this.attackTarget && this.attackCooldown <= 0) {
      this.doAttack();
      return; // 攻击时不移动
    }

    // 沿路径移动
    if (this.path.length > 0 && this.pathIndex < this.path.length) {
      const wp = this.path[this.pathIndex];
      const dx = wp.x - this.x, dy = wp.y - this.y;
      const d = Math.hypot(dx, dy);
      if (d < 8) {
        this.pathIndex++;
      } else {
        this.x += (dx / d) * this.speed * dt;
        this.y += (dy / d) * this.speed * dt;
      }
    } else {
      // 无路径时直接走向敌方水晶
      if (enemyCrystal) {
        const dx = enemyCrystal.x - this.x, dy = enemyCrystal.y - this.y;
        const d = Math.hypot(dx, dy);
        if (d > 8) { this.x += (dx / d) * this.speed * dt; this.y += (dy / d) * this.speed * dt; }
      }
    }
    // 每5秒重算路径
    if (Math.floor(gameTime * 1000) % 5000 < 50 && enemyCrystal) {
      this.path = aStarPath({ x: this.x, y: this.y }, { x: enemyCrystal.x, y: enemyCrystal.y }) || [];
      this.pathIndex = 0;
    }
  }
  doAttack() {
    if (!this.attackTarget || !this.attackTarget.alive) return;
    this.attackCooldown = MINION_ATK_INTERVAL / 1000;
    if (this.attackTarget instanceof Crystal) {
      this.attackTarget.takeDamage(MINION_DMG, 0);
    } else if (typeof this.attackTarget.hp === 'number') {
      this.attackTarget.hp -= MINION_DMG;
      if (this.attackTarget.hp <= 0) { this.attackTarget.hp = 0; this.attackTarget.alive = false; }
    }
  }
  serialize() {
    return { id: this.id, team: this.team, x: this.x, y: this.y, hp: this.hp, alive: this.alive, r: this.r };
  }
}

// ==================== 地图 ====================
const MAP_DATA = [];
(function buildMap() {
  const rows = [
    '1111111111111111111111111111111111111111',
    '1000000010000000000000000100000000000001',
    '1000000010000000000000000100000000000001',
    '1000000010000111000000000100000020000001',
    '1000000000000100000000000000000000000001',
    '1002000000000100000111000111000000000001',
    '1000000000000100000100000100000000200001',
    '1110011111000000000100000100000000000001',
    '1000000000000000000100000000000111000111',
    '1000000000000000000111000000000000000001',
    '1000000002000000000000000000000000000001',
    '1000011111110000000000000000200000000001',
    '1000000000000000000111000000000000000001',
    '1000000000000000000100000111000001110001',
    '1002000000000000000100000100000000000001',
    '1000000000000000000100000100000000000001',
    '1000001110000000000100000000000000000001',
    '1000000000000000000100000000200000000001',
    '1000000000002000000111000000000000000001',
    '1000010000000000000000000000000000000001',
    '1000010000000111000000000001100000000001',
    '1000000000000100000000000001000000000001',
    '1000000000000100000000000001000002000001',
    '1000200000000000000000000001000000000001',
    '1000000000000111001110000000000001110001',
    '1000000000000000000000000000000000000001',
    '1000000002000000000000000000000000000001',
    '1000000000000000000000000002000000000001',
    '1000000000000000000000000000000000000001',
    '1111111111111111111111111111111111111111',
  ];
  for (let y = 0; y < MAP_H; y++) {
    MAP_DATA[y] = [];
    for (let x = 0; x < MAP_W; x++) MAP_DATA[y][x] = parseInt(rows[y][x]);
  }
})();

function getAmmoSpawns() {
  const pts = [];
  for (let y = 0; y < MAP_H; y++)
    for (let x = 0; x < MAP_W; x++)
      if (MAP_DATA[y][x] === 2) pts.push({ x: x * TILE + TILE / 2, y: y * TILE + TILE / 2 });
  return pts;
}

const SPAWN_POINTS = [
  { x: 3 * TILE + TILE / 2, y: 3 * TILE + TILE / 2 },
  { x: 36 * TILE + TILE / 2, y: 3 * TILE + TILE / 2 },
  { x: 3 * TILE + TILE / 2, y: 26 * TILE + TILE / 2 },
  { x: 36 * TILE + TILE / 2, y: 26 * TILE + TILE / 2 },
  { x: 20 * TILE + TILE / 2, y: 15 * TILE + TILE / 2 },
];

const BOT_NAMES = ['红队AI', '橙队AI', '紫队AI', '绿队AI'];
const BOT_COLORS = ['#e74c3c', '#e67e22', '#9b59b6', '#2ecc71'];
const PLAYER_COLORS = ['#3498db', '#3498db', '#3498db', '#3498db', '#3498db'];

// ==================== 工具函数 ====================
function dist(a, b) { return Math.hypot(a.x - b.x, a.y - b.y); }
function norm(dx, dy) { const l = Math.hypot(dx, dy); return l ? { x: dx / l, y: dy / l } : { x: 0, y: 0 }; }
function isWall(wx, wy) {
  const tx = Math.floor(wx / TILE), ty = Math.floor(wy / TILE);
  if (tx < 0 || tx >= MAP_W || ty < 0 || ty >= MAP_H) return true;
  return MAP_DATA[ty][tx] === 1;
}
function resolveWallCollision(x, y, r) {
  const checks = [{ dx: 0, dy: -r }, { dx: r, dy: 0 }, { dx: 0, dy: r }, { dx: -r, dy: 0 },
                  { dx: -r, dy: -r }, { dx: r, dy: -r }, { dx: r, dy: r }, { dx: -r, dy: r }];
  for (const c of checks) {
    if (isWall(x + c.dx, y + c.dy)) {
      const cx = Math.floor((x + c.dx) / TILE) * TILE;
      const cy = Math.floor((y + c.dy) / TILE) * TILE;
      if (c.dx < 0) x = Math.max(x, cx + TILE + r);
      if (c.dx > 0) x = Math.min(x, cx - r);
      if (c.dy < 0) y = Math.max(y, cy + TILE + r);
      if (c.dy > 0) y = Math.min(y, cy - r);
    }
  }
  return { x, y };
}
function hasLineOfSight(x1, y1, x2, y2) {
  const dx = x2 - x1, dy = y2 - y1;
  const steps = Math.max(Math.abs(dx), Math.abs(dy)) / (TILE / 2);
  const sx = dx / steps, sy = dy / steps;
  let cx = x1, cy = y1;
  for (let i = 0; i < steps; i++) { cx += sx; cy += sy; if (isWall(cx, cy)) return false; }
  return true;
}
function generateId(len = 6) {
  const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789';
  let id = '';
  for (let i = 0; i < len; i++) id += chars[Math.floor(Math.random() * chars.length)];
  return id;
}

// ==================== AI 机器人 (服务端) ====================
class BotAI {
  constructor(id, x, y, color, name) {
    this.id = id; this.x = x; this.y = y;
    this.color = color; this.name = name;
    this.hp = MAX_HP; this.mag = MAG_SIZE; this.reserve = RESERVE_MAX;
    this.reloading = false; this.reloadTimer = 0;
    this.fireCooldown = 0; this.alive = true;
    this.angle = Math.random() * Math.PI * 2;
    this.vx = 0; this.vy = 0;
    this.isBot = true;
    this.state = 'patrol'; this.stateTimer = 0;
    this.patrolTarget = null;
  }

  get speed() { return BOT_SPEED; }
  get totalAmmo() { return this.mag + this.reserve; }

  update(dt, allPlayers, bullets, pickups) {
    if (!this.alive) return;
    if (this.fireCooldown > 0) this.fireCooldown -= dt;
    if (this.reloading) { this.reloadTimer -= dt; if (this.reloadTimer <= 0) this.finishReload(); }
    this.stateTimer -= dt;

    let nearestEnemy = null, nearestDist = Infinity;
    for (const p of allPlayers) {
      if (p === this || !p.alive) continue;
      const d = dist(this, p); if (d < nearestDist) { nearestDist = d; nearestEnemy = p; }
    }
    let nearestAmmo = null, nearestAmmoDist = Infinity;
    for (const pk of pickups) {
      if (!pk.active) continue;
      const d = dist(this, pk); if (d < nearestAmmoDist) { nearestAmmoDist = d; nearestAmmo = pk; }
    }
    const canSee = nearestEnemy && nearestDist < 500 && hasLineOfSight(this.x, this.y, nearestEnemy.x, nearestEnemy.y);

    let dodgeVx = 0, dodgeVy = 0;
    for (const b of bullets) {
      if (!b.alive || b.ownerId === this.id) continue;
      const d = dist(this, b);
      if (d < 60) { const away = norm(this.x - b.x, this.y - b.y); dodgeVx += away.x * (60 - d) / 60 * 300; dodgeVy += away.y * (60 - d) / 60 * 300; }
    }

    if (this.mag === 0 && this.reserve > 0 && !this.reloading) this.startReload();
    if (this.stateTimer <= 0) { this.state = 'patrol'; this.stateTimer = 2 + Math.random() * 3; }

    if (this.totalAmmo === 0 && nearestAmmo) this.state = 'seekAmmo';
    else if (canSee && this.mag > 0 && !this.reloading && nearestDist < 350) this.state = 'attack';
    else if (canSee && this.mag > 0 && !this.reloading) this.state = 'chase';
    else if (canSee && this.totalAmmo === 0) this.state = 'flee';

    let mx = 0, my = 0;
    switch (this.state) {
      case 'patrol':
        if (!this.patrolTarget || dist(this, this.patrolTarget) < 20) {
          this.patrolTarget = { x: CHAR_SIZE + Math.random() * (WORLD_W - CHAR_SIZE * 2), y: CHAR_SIZE + Math.random() * (WORLD_H - CHAR_SIZE * 2) };
          this.stateTimer = 3 + Math.random() * 4;
        }
        if (this.patrolTarget) { const d = norm(this.patrolTarget.x - this.x, this.patrolTarget.y - this.y); mx = d.x * this.speed; my = d.y * this.speed; }
        break;
      case 'chase':
        if (nearestEnemy) { const d = norm(nearestEnemy.x - this.x, nearestEnemy.y - this.y); mx = d.x * this.speed; my = d.y * this.speed; this.angle = Math.atan2(nearestEnemy.y - this.y, nearestEnemy.x - this.x); this.stateTimer = 1; }
        break;
      case 'attack':
        if (nearestEnemy) {
          const dir = norm(this.x - nearestEnemy.x, this.y - nearestEnemy.y);
          const strafe = { x: -dir.y, y: dir.x };
          const dd = nearestDist - 200;
          mx = dir.x * dd * 1.5 + strafe.x * 80 * (Math.sin(Date.now() / 800) > 0 ? 1 : -1);
          my = dir.y * dd * 1.5 + strafe.y * 80 * (Math.sin(Date.now() / 800) > 0 ? 1 : -1);
          const m = Math.hypot(mx, my); if (m > this.speed) { mx = mx / m * this.speed; my = my / m * this.speed; }
          this.angle = Math.atan2(nearestEnemy.y - this.y, nearestEnemy.x - this.x);
          this.tryShoot(bullets);
          this.stateTimer = 0.5;
        }
        break;
      case 'seekAmmo':
        if (nearestAmmo) { const d = norm(nearestAmmo.x - this.x, nearestAmmo.y - this.y); mx = d.x * this.speed; my = d.y * this.speed; }
        if (canSee && this.mag > 0) { this.tryShoot(bullets); }
        break;
      case 'flee':
        if (nearestEnemy) { const d = norm(this.x - nearestEnemy.x, this.y - nearestEnemy.y); mx = d.x * this.speed; my = d.y * this.speed; this.angle = Math.atan2(nearestEnemy.y - this.y, nearestEnemy.x - this.x); if (this.mag > 0 && !this.reloading) this.tryShoot(bullets); }
        break;
    }
    this.vx = mx + dodgeVx; this.vy = my + dodgeVy;

    const nx = this.x + this.vx * dt, ny = this.y + this.vy * dt;
    const res = resolveWallCollision(nx, ny, CHAR_SIZE * 0.7);
    this.x = Math.max(CHAR_SIZE, Math.min(WORLD_W - CHAR_SIZE, res.x));
    this.y = Math.max(CHAR_SIZE, Math.min(WORLD_H - CHAR_SIZE, res.y));
  }

  startReload() {
    if (this.reloading || this.reserve <= 0 || this.mag >= MAG_SIZE) return;
    this.reloading = true; this.reloadTimer = RELOAD_TIME / 1000;
  }
  finishReload() {
    const need = MAG_SIZE - this.mag, load = Math.min(need, this.reserve);
    this.mag += load; this.reserve -= load; this.reloading = false; this.reloadTimer = 0;
  }
  tryShoot(bullets) {
    if (!this.alive || this.reloading || this.mag <= 0 || this.fireCooldown > 0) return;
    this.mag--; this.fireCooldown = FIRE_INTERVAL / 1000;
    const bx = this.x + Math.cos(this.angle) * (CHAR_SIZE + 4);
    const by = this.y + Math.sin(this.angle) * (CHAR_SIZE + 4);
    const spread = (Math.random() - 0.5) * 0.15;
    const a = this.angle + spread;
    bullets.push({ x: bx, y: by, vx: Math.cos(a) * BULLET_SPEED, vy: Math.sin(a) * BULLET_SPEED, ownerId: this.id, alive: true });
  }

  serialize() {
    return { id: this.id, x: this.x, y: this.y, angle: this.angle, hp: this.hp, mag: this.mag, reserve: this.reserve, reloading: this.reloading, alive: this.alive, name: this.name, color: this.color, isBot: true };
  }
}

// ==================== 房间类 ====================
class Room {
  constructor(id, name, hostId) {
    this.id = id; this.name = name; this.hostId = hostId;
    this.state = 'lobby';
    this.gameMode = MODE_DM;    // 'deathmatch' | 'team_battle'
    this.humans = new Map();    // playerId → { id, ws, name, color, ready, team }
    this.playerTeams = new Map(); // playerId → 'blue' | 'red' (5v5)
    this.bots = [];
    this.bullets = [];
    this.pickups = [];
    this.crystals = [];
    this.minions = [];
    this.particles = [];
    this.tickTimer = null; this.tickNumber = 0;
    this.countdownTimer = null; this.countdownValue = 0;
    this.aliveCount = 0; this.gameTime = 0;
    this.killFeed = [];
    this.playerInputs = new Map();
    this.lastInputTime = new Map();
    this.playerStats = new Map();   // playerId → { kills, deaths, bonusDmg, bonusHp }
    this.respawnTimers = new Map(); // playerId → remaining seconds
    this.lobbyBots = 0;
    this.autoFillTimer = null;
    this.startAutoFill();
  }

  setGameMode(mode) {
    this.gameMode = mode;
    this.lobbyBots = 0;
    this.restartAutoFill();
    this.broadcastLobby();
  }

  assignTeam(playerId, team) {
    if (this.gameMode !== MODE_5V5) return;
    // 检查该阵营是否已满
    let count = 0;
    for (const [pid, t] of this.playerTeams) { if (t === team) count++; }
    if (count >= TEAM_SIZE) return;
    this.playerTeams.set(playerId, team);
    // 更新human记录
    const h = this.humans.get(playerId);
    if (h) h.team = team;
    this.broadcastLobby();
  }

  // 获取5v5大厅可用阵营信息
  getTeamInfo() {
    const blue = [], red = [];
    for (const [pid, h] of this.humans) {
      const t = this.playerTeams.get(pid);
      if (t === TEAM_BLUE) blue.push({ id: pid, name: h.name, isHost: pid === this.hostId });
      else if (t === TEAM_RED) red.push({ id: pid, name: h.name, isHost: pid === this.hostId });
    }
    return {
      blue: { players: blue, max: TEAM_SIZE, bots: Math.max(0, TEAM_SIZE - blue.length) },
      red:  { players: red,  max: TEAM_SIZE, bots: Math.max(0, TEAM_SIZE - red.length) },
    };
  }

  addHuman(clientId, ws, name) {
    const color = PLAYER_COLORS[this.humans.size % PLAYER_COLORS.length];
    const player = { id: clientId, ws, name, color, ready: true };
    this.humans.set(clientId, player);
    this.playerInputs.set(clientId, { keys: {}, mouseX: 0, mouseY: 0, shooting: false, reloading: false });
    this.lastInputTime.set(clientId, Date.now());
    // 真人加入时挤掉一个人机占位
    if (this.lobbyBots > 0 && (this.humans.size + this.lobbyBots) > this.maxSlots) {
      this.lobbyBots--;
    }
    this.restartAutoFill();
    this.broadcastLobby();
    return player;
  }

  removeHuman(playerId) {
    this.humans.delete(playerId);
    this.playerInputs.delete(playerId);
    this.lastInputTime.delete(playerId);
    if (this.state === 'playing') {
      const p = this.getStatePlayer(playerId);
      if (p && p.alive) { p.alive = false; this.aliveCount--; this.checkWin(); }
    }
    if (this.state === 'lobby') {
      this.restartAutoFill();
      this.broadcastLobby();
    }
    if (this.humans.size === 0 && this.state !== 'playing') this.scheduleDestroy();
    return this.humans.size;
  }

  // 自动填充人机 (每秒一个)
  startAutoFill() {
    if (this.autoFillTimer) return;
    this.autoFillTimer = setInterval(() => {
      if (this.state !== 'lobby') return;
      if (this.humans.size + this.lobbyBots >= this.maxSlots) {
        clearInterval(this.autoFillTimer); this.autoFillTimer = null;
        return;
      }
      this.lobbyBots++;
      this.broadcastLobby();
      if (this.humans.size + this.lobbyBots >= this.maxSlots) {
        clearInterval(this.autoFillTimer); this.autoFillTimer = null;
      }
    }, 1000);
  }

  stopAutoFill() {
    if (this.autoFillTimer) { clearInterval(this.autoFillTimer); this.autoFillTimer = null; }
  }

  get maxSlots() { return this.gameMode === MODE_5V5 ? TOTAL_SLOTS_5V5 : MAX_PLAYERS; }
  restartAutoFill() {
    this.stopAutoFill();
    if (this.state === 'lobby' && this.humans.size + this.lobbyBots < this.maxSlots) {
      this.startAutoFill();
    }
  }

  broadcastLobby() {
    this.broadcast({ type: 'room_update', room: this.getLobbyData() });
  }

  getStatePlayer(playerId) {
    for (const p of this.getAllPlayers()) if (p.id === playerId) return p;
    return null;
  }

  getAllPlayers() {
    const all = [];
    for (const [id, h] of this.humans) {
      const inp = this.playerInputs.get(id);
      const p = this.gamePlayers ? this.gamePlayers.get(id) : null;
      if (p) all.push(p);
      else {
        all.push({ id, x: SPAWN_POINTS[0].x, y: SPAWN_POINTS[0].y, angle: 0, hp: MAX_HP, mag: MAG_SIZE, reserve: RESERVE_MAX, reloading: false, alive: true, name: h.name, color: h.color, isBot: false, vx: 0, vy: 0 });
      }
    }
    for (const b of this.bots) all.push(b);
    return all;
  }

  setPlayerInput(playerId, input) {
    this.playerInputs.set(playerId, input);
    this.lastInputTime.set(playerId, Date.now());
    if (input.reloading) {
      const p = this.gamePlayers ? this.gamePlayers.get(playerId) : null;
      if (p && p.alive && !p.reloading && p.reserve > 0 && p.mag < MAG_SIZE) {
        p.reloading = true; p.reloadTimer = RELOAD_TIME / 1000;
      }
    }
  }

  startGame() {
    if (this.state !== 'lobby') return;
    this.stopAutoFill();
    this.beginGame();
  }

  beginGame() {
    this.state = 'playing'; this.bullets = []; this.particles = []; this.minions = [];
    this.gameTime = 0; this.tickNumber = 0; this.killFeed = [];
    this.stopAutoFill();
    this.lobbyBots = 0;
    const mapData = MAP_DATA;
    const baseInfo = { map: mapData, tileSize: TILE, mapW: MAP_W, mapH: MAP_H, worldW: WORLD_W, worldH: WORLD_H };

    if (this.gameMode === MODE_5V5) {
      this.beginTeamBattle(baseInfo);
    } else {
      this.beginDeathmatch(baseInfo);
    }

    for (const [id, h] of this.humans) {
      this.sendTo(h.ws, { type: 'game_start', ...baseInfo, yourId: id, gameMode: this.gameMode });
    }
  }

  beginDeathmatch(baseInfo) {
    const spawns = getAmmoSpawns();
    this.pickups = spawns.map(s => ({ x: s.x, y: s.y, active: true, respawnTimer: 0 }));

    const humanCount = this.humans.size;
    const botsNeeded = MAX_PLAYERS - humanCount;
    this.bots = [];
    for (let i = 0; i < botsNeeded; i++) {
      const sp = SPAWN_POINTS[humanCount + i] || SPAWN_POINTS[4];
      this.bots.push(new BotAI('bot_' + this.id + '_' + i,
        sp.x + (Math.random() - 0.5) * 60, sp.y + (Math.random() - 0.5) * 60,
        BOT_COLORS[i % BOT_COLORS.length], BOT_NAMES[i % BOT_NAMES.length]));
    }

    this.gamePlayers = new Map();
    let si = 0;
    for (const [id, h] of this.humans) {
      const sp = SPAWN_POINTS[si] || SPAWN_POINTS[4];
      this.gamePlayers.set(id, { id, x: sp.x, y: sp.y, angle: 0, hp: MAX_HP, mag: MAG_SIZE, reserve: RESERVE_MAX,
        reloading: false, reloadTimer: 0, fireCooldown: 0, alive: true,
        name: h.name, color: h.color, isBot: false, vx: 0, vy: 0, speed: PLAYER_SPEED, team: null });
      si++;
    }
    this.aliveCount = humanCount + this.bots.length;
    this.tickTimer = setInterval(() => this.tick(), TICK_RATE);
  }

  beginTeamBattle(baseInfo) {
    this.crystals = [
      new Crystal(TEAM_BLUE, CRYSTAL_POS.blue.x, CRYSTAL_POS.blue.y, 3*TILE+TILE/2, 3*TILE+TILE/2),
      new Crystal(TEAM_RED, CRYSTAL_POS.red.x, CRYSTAL_POS.red.y, 36*TILE+TILE/2, 26*TILE+TILE/2),
    ];
    this.pickups = [];
    this.playerStats = new Map();
    this.respawnTimers = new Map();
    this.minionSpawnAccum = 0;

    // 分配AI到双方阵营
    this.bots = [];
    const blueHumans = [...this.humans].filter(([id]) => this.playerTeams.get(id) === TEAM_BLUE);
    const redHumans  = [...this.humans].filter(([id]) => this.playerTeams.get(id) === TEAM_RED);
    // 未选阵营的随机分配
    for (const [id] of this.humans) {
      if (!this.playerTeams.has(id)) {
        if (blueHumans.length < TEAM_SIZE) { this.playerTeams.set(id, TEAM_BLUE); blueHumans.push([id]); }
        else { this.playerTeams.set(id, TEAM_RED); redHumans.push([id]); }
      }
    }

    // AI补齐双方到5人
    let botIdx = 0;
    for (let i = blueHumans.length; i < TEAM_SIZE; i++) {
      const sp = TEAM_SPAWNS.blue[i] || TEAM_SPAWNS.blue[4];
      const bot = new BotAI('botB_' + this.id + '_' + botIdx, sp.x, sp.y, BOT_COLORS[0], '蓝方AI' + (i+1));
      bot.team = TEAM_BLUE; bot.mag = MAG_SIZE; this.bots.push(bot); botIdx++;
    }
    for (let i = redHumans.length; i < TEAM_SIZE; i++) {
      const sp = TEAM_SPAWNS.red[i] || TEAM_SPAWNS.red[4];
      const bot = new BotAI('botR_' + this.id + '_' + botIdx, sp.x, sp.y, BOT_COLORS[1], '红方AI' + (i+1));
      bot.team = TEAM_RED; bot.mag = MAG_SIZE; this.bots.push(bot); botIdx++;
    }

    // 创建所有玩家
    this.gamePlayers = new Map();
    let bi = 0, ri = 0;
    for (const [id, h] of this.humans) {
      const team = this.playerTeams.get(id) || (bi < TEAM_SIZE ? TEAM_BLUE : TEAM_RED);
      const sp = team === TEAM_BLUE ? TEAM_SPAWNS.blue[bi++] : TEAM_SPAWNS.red[ri++];
      this.gamePlayers.set(id, { id, x: sp.x, y: sp.y, angle: 0,
        hp: MAX_HP, mag: MAG_SIZE, reserve: 999, reloading: false, reloadTimer: 0, fireCooldown: 0,
        alive: true, name: h.name, color: team === TEAM_BLUE ? '#4488ff' : '#ff4444', isBot: false,
        vx: 0, vy: 0, speed: PLAYER_SPEED, team, baseDmg: 1, bonusDmg: 0, bonusHp: 0, maxHp: MAX_HP });
      if (!this.playerStats.has(id)) this.playerStats.set(id, { kills: 0, deaths: 0, bonusDmg: 0, bonusHp: 0 });
    }

    this.aliveCount = this.gamePlayers.size + this.bots.length;
    this.tickTimer = setInterval(() => this.teamBattleTick(), TICK_RATE);
  }

  tick() {
    const dt = TICK_RATE / 1000;
    this.gameTime += dt;
    this.tickNumber++;

    // 处理人类玩家输入
    for (const [id, p] of this.gamePlayers) {
      if (!p.alive) continue;
      const inp = this.playerInputs.get(id);
      if (!inp) continue;

      let mx = 0, my = 0;
      if (inp.keys['w'] || inp.keys['arrowup']) my -= 1;
      if (inp.keys['s'] || inp.keys['arrowdown']) my += 1;
      if (inp.keys['a'] || inp.keys['arrowleft']) mx -= 1;
      if (inp.keys['d'] || inp.keys['arrowright']) mx += 1;
      if (mx !== 0 || my !== 0) { const n = norm(mx, my); p.vx = n.x * PLAYER_SPEED; p.vy = n.y * PLAYER_SPEED; }
      else { p.vx = 0; p.vy = 0; }

      p.angle = Math.atan2(inp.mouseY, inp.mouseX); // 客户端发送鼠标相对于玩家的方向

      if (p.fireCooldown > 0) p.fireCooldown -= dt;
      if (p.reloading) { p.reloadTimer -= dt; if (p.reloadTimer <= 0) this.finishHumanReload(p); }

      // 自动瞄准射击
      if (inp.shooting && p.mag > 0 && !p.reloading && p.fireCooldown <= 0) {
        const target = this.findAutoAimTarget(p);
        if (target) {
          p.angle = Math.atan2(target.y - p.y, target.x - p.x);
        }
        this.humanShoot(p);
      }

      // 自动换弹
      if (p.mag === 0 && p.reserve > 0 && !p.reloading) {
        p.reloading = true; p.reloadTimer = RELOAD_TIME / 1000;
      }

      // 移动 + 碰撞
      const nx = p.x + p.vx * dt, ny = p.y + p.vy * dt;
      const res = resolveWallCollision(nx, ny, CHAR_SIZE * 0.7);
      p.x = Math.max(CHAR_SIZE, Math.min(WORLD_W - CHAR_SIZE, res.x));
      p.y = Math.max(CHAR_SIZE, Math.min(WORLD_H - CHAR_SIZE, res.y));
    }

    // 更新机器人
    const allPlayers = this.getAllPlayers();
    for (const bot of this.bots) bot.update(dt, allPlayers, this.bullets, this.pickups);

    // 更新子弹
    for (const b of this.bullets) {
      b.x += b.vx * dt; b.y += b.vy * dt;
      if (isWall(b.x, b.y)) b.alive = false;
      if (b.x < 0 || b.x > WORLD_W || b.y < 0 || b.y > WORLD_H) b.alive = false;
    }

    // 碰撞检测
    for (const b of this.bullets) {
      if (!b.alive) continue;
      for (const p of allPlayers) {
        if (!p.alive || p.id === b.ownerId) continue;
        if (dist(b, p) < CHAR_SIZE + BULLET_R) {
          b.alive = false;
          p.hp--;
          if (p.hp <= 0) { p.hp = 0; p.alive = false; this.aliveCount--; this.onPlayerDeath(p, b.ownerId); }
          break;
        }
      }
    }

    // 弹药拾取
    for (const pk of this.pickups) {
      if (!pk.active) { pk.respawnTimer -= TICK_RATE; if (pk.respawnTimer <= 0) pk.active = true; continue; }
      for (const p of allPlayers) {
        if (!p.alive) continue;
        if (dist(p, pk) < 24) { p.mag = MAG_SIZE; p.reserve = RESERVE_MAX; p.reloading = false; p.reloadTimer = 0; pk.active = false; pk.respawnTimer = PICKUP_RESPAWN; break; }
      }
    }

    // 清理子弹
    this.bullets = this.bullets.filter(b => b.alive);

    // 检查胜利
    if (this.aliveCount <= 1) this.endGame();

    // 广播状态
    this.broadcastState();
  }

  findAutoAimTarget(shooter) {
    let best = null, bestDist = AUTO_AIM_RANGE;
    for (const p of this.getAllPlayers()) {
      if (!p.alive || p.id === shooter.id) continue;
      const d = dist(shooter, p);
      if (d < bestDist && hasLineOfSight(shooter.x, shooter.y, p.x, p.y)) {
        best = p; bestDist = d;
      }
    }
    return best;
  }

  humanShoot(p) {
    p.mag--;
    p.fireCooldown = FIRE_INTERVAL / 1000;
    const bx = p.x + Math.cos(p.angle) * (CHAR_SIZE + 4);
    const by = p.y + Math.sin(p.angle) * (CHAR_SIZE + 4);
    this.bullets.push({ x: bx, y: by, vx: Math.cos(p.angle) * BULLET_SPEED, vy: Math.sin(p.angle) * BULLET_SPEED, ownerId: p.id, alive: true });
  }

  finishHumanReload(p) {
    const need = MAG_SIZE - p.mag, load = Math.min(need, p.reserve);
    p.mag += load; p.reserve -= load; p.reloading = false; p.reloadTimer = 0;
  }

  onPlayerDeath(victim, killerId) {
    const killer = this.getStatePlayer(killerId);
    const kn = killer ? killer.name : '未知';
    this.killFeed.push({ killer: kn, victim: victim.name, time: 3 });
    if (this.killFeed.length > 6) this.killFeed.shift();
  }

  checkWin() {
    if (this.aliveCount <= 1) this.endGame();
  }

  endGame() {
    clearInterval(this.tickTimer); this.tickTimer = null;
    this.state = 'finished';
    const survivor = this.getAllPlayers().find(p => p.alive);
    this.broadcast({ type: 'game_over', winner: survivor ? survivor.name : '无人', winnerId: survivor ? survivor.id : null });

    // 5秒后回到大厅
    setTimeout(() => {
      if (this.state === 'finished') {
        this.state = 'lobby';
        this.bots = []; this.bullets = []; this.pickups = [];
        this.gamePlayers = null; this.killFeed = [];
        this.lobbyBots = 0;
        this.broadcast({ type: 'return_to_lobby' });
        this.restartAutoFill();
      }
    }, 5000);
  }

  // ==================== 5v5 模式游戏循环 ====================
  teamBattleTick() {
    const dt = TICK_RATE / 1000;
    this.gameTime += dt;
    this.tickNumber++;

    // 水晶更新 + 攻击
    const allPlayersNow = this.getAllPlayers();
    for (const c of this.crystals) {
      c.update(dt, this.gameTime);
      const target = c.findTarget(allPlayersNow, this.minions);
      if (target) c.tryAttack(target);
    }

    // 检查水晶是否被摧毁
    const deadCrystal = this.crystals.find(c => !c.alive);
    if (deadCrystal) {
      const winTeam = deadCrystal.team === TEAM_BLUE ? TEAM_RED : TEAM_BLUE;
      this.endTeamBattle(winTeam);
      return;
    }

    // 复活倒计时
    for (const [id, timer] of this.respawnTimers) {
      timer.remaining -= dt * 1000;
      if (timer.remaining <= 0) {
        this.respawnTimers.delete(id);
        this.respawnPlayer(id);
      }
    }

    // 小兵生成 (90秒后)
    this.minionSpawnAccum += dt * 1000;
    if (this.gameTime * 1000 >= MINION_SPAWN_DELAY && this.minionSpawnAccum >= MINION_INTERVAL) {
      this.minionSpawnAccum -= MINION_INTERVAL;
      for (const c of this.crystals) {
        if (!c.alive) continue;
        const enemyCrystal = this.crystals.find(cc => cc.team !== c.team && cc.alive);
        if (!enemyCrystal) continue;
        const path = aStarPath({ x: c.x, y: c.y }, { x: enemyCrystal.x, y: enemyCrystal.y }) || [];
        const id = 'minion_' + this.tickNumber + '_' + c.team;
        this.minions.push(new Minion(id, c.team, c.x, c.y, enemyCrystal, path));
      }
    }

    // 处理人类玩家
    const allPlayers = this.getAllPlayers();
    for (const [id, p] of this.gamePlayers) {
      if (!p.alive) continue;
      const inp = this.playerInputs.get(id);
      if (!inp) continue;

      let mx = 0, my = 0;
      if (inp.keys['w'] || inp.keys['arrowup']) my -= 1;
      if (inp.keys['s'] || inp.keys['arrowdown']) my += 1;
      if (inp.keys['a'] || inp.keys['arrowleft']) mx -= 1;
      if (inp.keys['d'] || inp.keys['arrowright']) mx += 1;
      if (mx !== 0 || my !== 0) { const n = norm(mx, my); p.vx = n.x * PLAYER_SPEED; p.vy = n.y * PLAYER_SPEED; }
      else { p.vx = 0; p.vy = 0; }

      p.angle = Math.atan2(inp.mouseY, inp.mouseX);
      if (p.fireCooldown > 0) p.fireCooldown -= dt;
      // 5v5: 无限备弹, 弹夹5发需换弹
      p.reserve = 999;
      if (p.reloading) { p.reloadTimer -= dt; if (p.reloadTimer <= 0) { const need = MAG_SIZE - p.mag; const load = Math.min(need, p.reserve); p.mag += load; p.reserve -= load; p.reloading = false; } }
      if (p.mag === 0 && !p.reloading) { p.reloading = true; p.reloadTimer = RELOAD_TIME / 1000; }
      if (inp.reloading && !p.reloading && p.mag < MAG_SIZE) { p.reloading = true; p.reloadTimer = RELOAD_TIME / 1000; }

      if (inp.shooting && p.mag > 0 && !p.reloading && p.fireCooldown <= 0) {
        const target = this.findTeamAutoAimTarget(p);
        if (target) p.angle = Math.atan2(target.y - p.y, target.x - p.x);
        this.teamShoot(p);
      }

      // 回血圈检测
      const myCrystal = this.crystals.find(c => c.team === p.team && c.alive);
      if (myCrystal && myCrystal.isInHealZone(p.x, p.y)) {
        p.hp = Math.min(p.maxHp, p.hp + HEAL_RATE * dt);
      }

      const nx = p.x + p.vx * dt, ny = p.y + p.vy * dt;
      const res = resolveWallCollision(nx, ny, CHAR_SIZE * 0.7);
      p.x = Math.max(CHAR_SIZE, Math.min(WORLD_W - CHAR_SIZE, res.x));
      p.y = Math.max(CHAR_SIZE, Math.min(WORLD_H - CHAR_SIZE, res.y));
    }

    // 更新机器人
    for (const bot of this.bots) this.updateTeamBot(bot, dt, allPlayers);

    // 更新小兵
    for (const m of this.minions) m.update(dt, allPlayers, this.crystals, this.minions, this.gameTime);
    this.minions = this.minions.filter(m => m.alive);

    // 更新子弹
    for (const b of this.bullets) {
      b.x += b.vx * dt; b.y += b.vy * dt;
      if (isWall(b.x, b.y)) b.alive = false;
      if (b.x < 0 || b.x > WORLD_W || b.y < 0 || b.y > WORLD_H) b.alive = false;
    }

    // 碰撞: 子弹 vs 水晶
    for (const b of this.bullets) {
      if (!b.alive) continue;
      for (const c of this.crystals) {
        if (!c.alive || c.team === b.team) continue;
        if (Math.hypot(b.x - c.x, b.y - c.y) < c.r + BULLET_R) {
          b.alive = false;
          c.takeDamage(1 + (b.bonusDmg || 0), this.gameTime);
          break;
        }
      }
    }

    // 碰撞: 子弹 vs 玩家 (无友伤)
    for (const b of this.bullets) {
      if (!b.alive) continue;
      for (const p of allPlayers) {
        if (!p.alive || p.id === b.ownerId) continue;
        if (p.team === b.team) continue; // 无友伤
        if (Math.hypot(b.x - p.x, b.y - p.y) < CHAR_SIZE + BULLET_R) {
          b.alive = false;
          const dmg = 1 + (b.bonusDmg || 0);
          p.hp -= dmg;
          if (p.hp <= 0) { p.hp = 0; p.alive = false; this.onTeamKill(b.ownerId, p.id); }
          break;
        }
      }
    }

    // 碰撞: 子弹 vs 小兵
    for (const b of this.bullets) {
      if (!b.alive) continue;
      for (const m of this.minions) {
        if (!m.alive || m.team === b.team) continue;
        if (Math.hypot(b.x - m.x, b.y - m.y) < m.r + BULLET_R) {
          b.alive = false; m.hp -= 1;
          if (m.hp <= 0) { m.hp = 0; m.alive = false; }
          break;
        }
      }
    }

    // 小兵攻击玩家
    for (const m of this.minions) {
      if (!m.alive) continue;
      if (m.attackTarget && m.attackCooldown <= 0 && typeof m.attackTarget.hp === 'number' && m.attackTarget.alive) {
        m.doAttack();
        if (m.attackTarget.hp <= 0) {
          m.attackTarget.alive = false;
          if (!m.attackTarget.isBot && this.gamePlayers.has(m.attackTarget.id)) {
            this.onTeamKill(null, m.attackTarget.id);
          }
        }
      }
    }

    // 清理子弹
    this.bullets = this.bullets.filter(b => b.alive);
    this.broadcastTeamState();
  }

  findTeamAutoAimTarget(shooter) {
    let best = null, bestDist = AUTO_AIM_RANGE;
    for (const p of this.getAllPlayers()) {
      if (!p.alive || p.id === shooter.id) continue;
      if (p.team === shooter.team) continue; // 不锁定队友
      const d = Math.hypot(shooter.x - p.x, shooter.y - p.y);
      if (d < bestDist && hasLineOfSight(shooter.x, shooter.y, p.x, p.y)) {
        // 也锁定敌方小兵
        best = p; bestDist = d;
      }
    }
    // 检查小兵
    for (const m of this.minions) {
      if (!m.alive || m.team === shooter.team) continue;
      const d = Math.hypot(shooter.x - m.x, shooter.y - m.y);
      if (d < bestDist && hasLineOfSight(shooter.x, shooter.y, m.x, m.y)) {
        best = m; bestDist = d;
      }
    }
    return best;
  }

  teamShoot(p) {
    p.fireCooldown = FIRE_INTERVAL / 1000;
    const bx = p.x + Math.cos(p.angle) * (CHAR_SIZE + 4);
    const by = p.y + Math.sin(p.angle) * (CHAR_SIZE + 4);
    this.bullets.push({ x: bx, y: by, vx: Math.cos(p.angle) * BULLET_SPEED, vy: Math.sin(p.angle) * BULLET_SPEED, ownerId: p.id, alive: true, team: p.team, bonusDmg: p.bonusDmg || 0 });
  }

  updateTeamBot(bot, dt, allPlayers) {
    if (!bot.alive) return;
    if (bot.fireCooldown > 0) bot.fireCooldown -= dt;
    // 换弹逻辑
    bot.reserve = 999;
    if (bot.reloading) { bot.reloadTimer -= dt; if (bot.reloadTimer <= 0) { const need = MAG_SIZE - (bot.mag||0); const load = Math.min(need, bot.reserve||0); bot.mag = (bot.mag||0) + load; bot.reserve -= load; bot.reloading = false; } }
    if ((bot.mag||0) === 0 && !bot.reloading) { bot.reloading = true; bot.reloadTimer = RELOAD_TIME / 1000; }

    const myCrystal = this.crystals.find(c => c.team === bot.team && c.alive);
    // 低血量撤退回血
    if (bot.hp < 2 && myCrystal) {
      const hx = myCrystal.healX, hy = myCrystal.healY;
      const toHeal = Math.hypot(bot.x - hx, bot.y - hy);
      if (toHeal > HEAL_RADIUS) {
        // 重新计算到回血圈的路径
        if (!bot._pathRecalc || Date.now() - bot._pathRecalc > 3000) {
          bot._path = aStarPath({ x: bot.x, y: bot.y }, { x: hx, y: hy });
          bot._pathIdx = 0; bot._pathRecalc = Date.now();
        }
        if (bot._path && bot._path.length > 0 && bot._pathIdx < bot._path.length) {
          const wp = bot._path[bot._pathIdx];
          const dx = wp.x - bot.x, dy = wp.y - bot.y;
          const d = Math.hypot(dx, dy);
          if (d < 12) bot._pathIdx++;
          else { bot.vx = (dx/d) * BOT_SPEED; bot.vy = (dy/d) * BOT_SPEED; bot.angle = Math.atan2(dy, dx); }
        } else {
          const dir = norm(hx - bot.x, hy - bot.y);
          bot.vx = dir.x * BOT_SPEED; bot.vy = dir.y * BOT_SPEED;
          bot.angle = Math.atan2(dir.y, dir.x);
        }
      } else {
        // 在回血圈内, 停止回血
        bot.vx = 0; bot.vy = 0;
        bot.hp = Math.min(bot.maxHp || MAX_HP, bot.hp + HEAL_RATE * dt);
      }
    } else {
      // 正常战斗: 寻找敌方
      let nearestEnemy = null, nearestDist = Infinity;
      for (const p of allPlayers) {
        if (p === bot || !p.alive || p.team === bot.team) continue;
        const d = Math.hypot(bot.x - p.x, bot.y - p.y);
        if (d < nearestDist) { nearestDist = d; nearestEnemy = p; }
      }
      for (const m of this.minions) {
        if (!m.alive || m.team === bot.team) continue;
        const d = Math.hypot(bot.x - m.x, bot.y - m.y);
        if (d < nearestDist) { nearestDist = d; nearestEnemy = m; }
      }
      const enemyCrystal = this.crystals.find(c => c.team !== bot.team && c.alive);
      if (enemyCrystal) {
        const d = Math.hypot(bot.x - enemyCrystal.x, bot.y - enemyCrystal.y);
        if (d < nearestDist + enemyCrystal.r) { nearestDist = d; nearestEnemy = enemyCrystal; }
      }

      if (nearestEnemy) {
        bot.angle = Math.atan2(nearestEnemy.y - bot.y, nearestEnemy.x - bot.x);
        // A* 寻路避免卡墙
        if (!bot._pathRecalc || Date.now() - bot._pathRecalc > 3000 || isWall(bot.x + bot.vx * dt, bot.y + bot.vy * dt)) {
          bot._path = aStarPath({ x: bot.x, y: bot.y }, { x: nearestEnemy.x, y: nearestEnemy.y });
          bot._pathIdx = 0; bot._pathRecalc = Date.now();
        }
        if (bot._path && bot._path.length > 1 && bot._pathIdx < bot._path.length) {
          const wp = bot._path[bot._pathIdx];
          const dx = wp.x - bot.x, dy = wp.y - bot.y;
          const d = Math.hypot(dx, dy);
          if (d < 12) bot._pathIdx++;
          else { bot.vx = (dx/d) * BOT_SPEED; bot.vy = (dy/d) * BOT_SPEED; }
        } else {
          const dir = norm(nearestEnemy.x - bot.x, nearestEnemy.y - bot.y);
          bot.vx = dir.x * BOT_SPEED; bot.vy = dir.y * BOT_SPEED;
        }
        // 射击
        if (bot.fireCooldown <= 0 && (bot.mag||0) > 0 && !bot.reloading && hasLineOfSight(bot.x, bot.y, nearestEnemy.x, nearestEnemy.y)) {
          bot.fireCooldown = FIRE_INTERVAL / 1000;
          bot.mag = (bot.mag||MAG_SIZE) - 1;
          const bx = bot.x + Math.cos(bot.angle) * (CHAR_SIZE + 4);
          const by = bot.y + Math.sin(bot.angle) * (CHAR_SIZE + 4);
          const spread = (Math.random() - 0.5) * 0.15;
          const a = bot.angle + spread;
          this.bullets.push({ x: bx, y: by, vx: Math.cos(a) * BULLET_SPEED, vy: Math.sin(a) * BULLET_SPEED, ownerId: bot.id, alive: true, team: bot.team, bonusDmg: bot.bonusDmg || 0 });
        }
      } else {
        // 无目标时往敌方水晶方向移动
        if (enemyCrystal) {
          if (!bot._pathRecalc || Date.now() - bot._pathRecalc > 5000) {
            bot._path = aStarPath({ x: bot.x, y: bot.y }, { x: enemyCrystal.x, y: enemyCrystal.y });
            bot._pathIdx = 0; bot._pathRecalc = Date.now();
          }
          if (bot._path && bot._path.length > 1 && bot._pathIdx < bot._path.length) {
            const wp = bot._path[bot._pathIdx];
            const dx = wp.x - bot.x, dy = wp.y - bot.y;
            if (Math.hypot(dx,dy) < 12) bot._pathIdx++;
            else { bot.vx = (dx/Math.hypot(dx,dy)) * BOT_SPEED; bot.vy = (dy/Math.hypot(dx,dy)) * BOT_SPEED; bot.angle = Math.atan2(dy, dx); }
          }
        }
      }
    }

    const nx = bot.x + bot.vx * dt, ny = bot.y + bot.vy * dt;
    const res = resolveWallCollision(nx, ny, CHAR_SIZE * 0.7);
    bot.x = Math.max(CHAR_SIZE, Math.min(WORLD_W - CHAR_SIZE, res.x));
    bot.y = Math.max(CHAR_SIZE, Math.min(WORLD_H - CHAR_SIZE, res.y));
  }

  onTeamKill(killerId, victimId) {
    // 击杀者奖励
    if (killerId) {
      const stats = this.playerStats.get(killerId);
      const killer = this.getStatePlayer(killerId);
      if (stats && killer) {
        stats.kills = (stats.kills || 0) + 1;
        stats.bonusDmg = (stats.bonusDmg || 0) + KILL_DMG_BONUS;
        stats.bonusHp = (stats.bonusHp || 0) + KILL_HP_BONUS;
        killer.bonusDmg = stats.bonusDmg;
        killer.bonusHp = stats.bonusHp;
        killer.maxHp = MAX_HP + stats.bonusHp;
        killer.hp = Math.min(killer.hp + KILL_HP_BONUS, killer.maxHp); // 击杀回血
      }
      this.killFeed.push({ killer: killer?.name || '未知', victim: this.getStatePlayer(victimId)?.name || '未知', time: 3 });
    }
    // 记录死亡 + 清空被杀者加成
    const vStats = this.playerStats.get(victimId);
    if (vStats) { vStats.deaths = (vStats.deaths || 0) + 1; vStats.bonusDmg = 0; vStats.bonusHp = 0; }
    const victim = this.getStatePlayer(victimId);
    if (victim) { victim.bonusDmg = 0; victim.bonusHp = 0; victim.maxHp = MAX_HP; }
    // 设置复活
    this.respawnTimers.set(victimId, { remaining: RESPAWN_TIME });
    if (this.killFeed.length > 6) this.killFeed.shift();
  }

  respawnPlayer(playerId) {
    const p = this.getStatePlayer(playerId);
    if (!p) return;
    p.alive = true;
    p.maxHp = MAX_HP; p.bonusDmg = 0; p.bonusHp = 0;
    p.hp = p.maxHp;
    p.mag = MAG_SIZE; p.reserve = 999;
    p.reloading = false; p.reloadTimer = 0;
    const team = p.team || this.playerTeams.get(playerId) || TEAM_BLUE;
    const sp = TEAM_SPAWNS[team][Math.floor(Math.random() * TEAM_SIZE)];
    p.x = sp.x + (Math.random() - 0.5) * 40;
    p.y = sp.y + (Math.random() - 0.5) * 40;
  }

  endTeamBattle(winTeam) {
    clearInterval(this.tickTimer); this.tickTimer = null;
    this.state = 'finished';
    // 收集战绩
    const stats = [];
    for (const [id, s] of this.playerStats) {
      const p = this.getStatePlayer(id) || { name: '未知' };
      stats.push({ name: p.name || '未知', kills: s.kills || 0, deaths: s.deaths || 0, team: p.team || '未知' });
    }
    this.broadcast({ type: 'game_over', winner: winTeam === TEAM_BLUE ? '蓝方' : '红方', winnerTeam: winTeam, stats });

    setTimeout(() => {
      if (this.state === 'finished') {
        this.state = 'lobby';
        this.bots = []; this.bullets = []; this.pickups = []; this.minions = []; this.crystals = [];
        this.gamePlayers = null; this.killFeed = []; this.playerStats = new Map();
        this.respawnTimers = new Map();
        this.lobbyBots = 0;
        this.broadcast({ type: 'return_to_lobby' });
        this.restartAutoFill();
      }
    }, 8000);
  }

  broadcastTeamState() {
    const allPlayers = this.getAllPlayers();
    const state = {
      type: 'game_state',
      tick: this.tickNumber,
      gameTime: this.gameTime,
      gameMode: MODE_5V5,
      players: allPlayers.map(p => ({
        id: p.id, x: p.x, y: p.y, angle: p.angle,
        hp: p.hp, maxHp: p.maxHp || MAX_HP, mag: p.mag, reserve: p.reserve,
        reloading: p.reloading || false, alive: p.alive,
        name: p.name, color: p.color, isBot: p.isBot,
        vx: p.vx || 0, vy: p.vy || 0, team: p.team
      })),
      bullets: this.bullets.filter(b => b.alive).map(b => ({ x: b.x, y: b.y, vx: b.vx, vy: b.vy, team: b.team })),
      crystals: this.crystals.map(c => c.serialize()),
      minions: this.minions.filter(m => m.alive).map(m => m.serialize()),
      respawnTimers: [...this.respawnTimers].map(([id, t]) => ({ id, remaining: Math.ceil(t.remaining / 1000) })),
      killFeed: this.killFeed.filter(kf => kf.time > 0),
      aliveCount: allPlayers.filter(p => p.alive).length + this.minions.filter(m => m.alive).length,
    };
    for (const kf of this.killFeed) kf.time -= TICK_RATE / 1000;
    this.killFeed = this.killFeed.filter(kf => kf.time > 0);
    for (const [id, h] of this.humans) {
      if (h.ws.readyState === 1) this.sendTo(h.ws, state);
    }
  }

  broadcastState() {
    const allPlayers = this.getAllPlayers();
    const state = {
      type: 'game_state',
      tick: this.tickNumber,
      gameTime: this.gameTime,
      aliveCount: this.aliveCount,
      players: allPlayers.map(p => ({
        id: p.id, x: p.x, y: p.y, angle: p.angle,
        hp: p.hp, mag: p.mag, reserve: p.reserve,
        reloading: p.reloading, alive: p.alive,
        name: p.name, color: p.color, isBot: p.isBot,
        vx: p.vx || 0, vy: p.vy || 0
      })),
      bullets: this.bullets.filter(b => b.alive).map(b => ({ x: b.x, y: b.y, vx: b.vx, vy: b.vy })),
      pickups: this.pickups.map(pk => ({ x: pk.x, y: pk.y, active: pk.active })),
      killFeed: this.killFeed.filter(kf => kf.time > 0)
    };
    // 更新 killFeed 计时
    for (const kf of this.killFeed) kf.time -= TICK_RATE / 1000;
    this.killFeed = this.killFeed.filter(kf => kf.time > 0);

    for (const [id, h] of this.humans) {
      if (h.ws.readyState === 1) this.sendTo(h.ws, state);
    }
  }

  broadcast(msg) {
    const data = JSON.stringify(msg);
    for (const [id, h] of this.humans) {
      if (h.ws.readyState === 1) h.ws.send(data);
    }
  }

  sendTo(ws, msg) {
    if (ws.readyState === 1) ws.send(JSON.stringify(msg));
  }

  scheduleDestroy() {
    setTimeout(() => {
      if (this.humans.size === 0 && this.state === 'lobby') {
        // 由 GameServer 清理
        if (this.onEmpty) this.onEmpty(this.id);
      }
    }, 30000);
  }

  getInfo() {
    const max = this.gameMode === MODE_5V5 ? TOTAL_SLOTS_5V5 : MAX_PLAYERS;
    return {
      id: this.id, name: this.name,
      playerCount: this.humans.size + this.lobbyBots,
      maxPlayers: max,
      state: this.state,
      hostId: this.hostId,
      gameMode: this.gameMode
    };
  }

  getLobbyData() {
    const players = [];
    for (const [id, h] of this.humans) {
      const t = this.playerTeams.get(id);
      players.push({ id, name: h.name, isHost: id === this.hostId, team: t || null });
    }
    for (let i = 0; i < this.lobbyBots; i++) {
      players.push({ id: 'bot_ph_' + i, name: '人机 ' + (i + 1), isHost: false, isBot: true, team: null });
    }
    const max = this.gameMode === MODE_5V5 ? TOTAL_SLOTS_5V5 : MAX_PLAYERS;
    const data = { id: this.id, name: this.name, players, hostId: this.hostId, state: this.state, maxPlayers: max, lobbyBots: this.lobbyBots, gameMode: this.gameMode };
    if (this.gameMode === MODE_5V5) data.teams = this.getTeamInfo();
    return data;
  }
}

// ==================== 游戏服务器 ====================
class GameServer {
  constructor() {
    this.rooms = new Map();
    this.clients = new Map(); // ws → { id, name, roomId }
    this.matchmakingQueue = [];
  }

  handleConnection(ws) {
    const clientId = generateId(8);
    this.clients.set(ws, { id: clientId, name: '玩家', roomId: null });
    this.sendTo(ws, { type: 'connected', clientId });
    console.log('客户端连接:', clientId);

    ws.on('message', (raw) => {
      const text = raw.toString().trim();
      if (!text || text[0] !== '{') {
        console.log('忽略非JSON:', text.substring(0, 80));
        return;
      }
      let msg;
      try {
        msg = JSON.parse(text);
      } catch (e) {
        console.log('JSON解析失败:', text.substring(0, 80));
        return;
      }
      console.log('收到:', msg.type, 'from', this.clients.get(ws)?.name);
      try {
        this.handleMessage(ws, msg);
      } catch (e) {
        console.error('处理消息出错:', msg.type, e.message);
      }
    });

    ws.on('close', () => this.handleDisconnect(ws));
    ws.on('error', () => {});
  }

  handleMessage(ws, msg) {
    const client = this.clients.get(ws);
    if (!client) return;

    switch (msg.type) {
      case 'set_name':
        client.name = (msg.name || '玩家').substring(0, 12);
        this.sendTo(ws, { type: 'name_set', name: client.name });
        break;

      case 'create_room':
        this.createRoom(ws, msg.roomName || (client.name + '的房间'));
        break;

      case 'join_room':
        this.joinRoom(ws, msg.roomId);
        break;

      case 'quick_match':
        this.quickMatch(ws);
        break;

      case 'leave_room':
        this.leaveRoom(ws);
        break;

      case 'start_game':
        this.handleStartGame(ws);
        break;

      case 'get_rooms':
        this.sendRoomList(ws);
        break;

      case 'input':
        this.handleInput(ws, msg);
        break;

      case 'ready':
        this.handleReady(ws);
        break;

      case 'set_mode':
        this.handleSetMode(ws, msg.mode);
        break;

      case 'assign_team':
        this.handleAssignTeam(ws, msg.team);
        break;

      case 'quick_match_5v5':
        this.quickMatch5v5(ws);
        break;

      default:
        break;
    }
  }

  createRoom(ws, roomName) {
    const client = this.clients.get(ws);
    if (!client) return;
    if (client.roomId) { this.sendTo(ws, { type: 'error', message: '已在房间中' }); return; }

    const roomId = generateId(6);
    const room = new Room(roomId, roomName, client.id);
    room.onEmpty = (rid) => this.rooms.delete(rid);
    const player = room.addHuman(client.id, ws, client.name);
    client.roomId = roomId;
    this.rooms.set(roomId, room);
    this.sendTo(ws, { type: 'room_joined', room: room.getLobbyData(), yourId: player.id });
  }

  joinRoom(ws, roomId) {
    const client = this.clients.get(ws);
    if (!client) return;
    if (client.roomId) { this.sendTo(ws, { type: 'error', message: '已在房间中' }); return; }

    const room = this.rooms.get(roomId);
    if (!room) { this.sendTo(ws, { type: 'error', message: '房间不存在' }); return; }
    if (room.state !== 'lobby') { this.sendTo(ws, { type: 'error', message: '游戏已开始' }); return; }
    if (room.humans.size >= room.maxSlots) { this.sendTo(ws, { type: 'error', message: '房间已满' }); return; }

    const player = room.addHuman(client.id, ws, client.name);
    client.roomId = roomId;
    this.sendTo(ws, { type: 'room_joined', room: room.getLobbyData(), yourId: player.id });
    room.broadcast({ type: 'room_update', room: room.getLobbyData() });
  }

  quickMatch(ws) {
    const client = this.clients.get(ws);
    if (!client) return;
    if (client.roomId) { this.sendTo(ws, { type: 'error', message: '已在房间中' }); return; }

    // 寻找可用房间
    for (const [id, room] of this.rooms) {
      if (room.state === 'lobby' && room.humans.size < room.maxSlots) {
        this.joinRoom(ws, id);
        return;
      }
    }
    // 没有可用房间, 创建新房间
    this.createRoom(ws, '快速匹配 #' + generateId(4));
  }

  leaveRoom(ws) {
    const client = this.clients.get(ws);
    if (!client || !client.roomId) return;
    const room = this.rooms.get(client.roomId);
    if (!room) { client.roomId = null; return; }

    const remaining = room.removeHuman(client.id);
    client.roomId = null;

    if (remaining > 0) {
      // 如果 host 离开, 转移 host
      if (client.id === room.hostId) {
        const first = room.humans.values().next().value;
        if (first) room.hostId = first.id;
      }
      room.broadcast({ type: 'room_update', room: room.getLobbyData() });
    }
    this.sendTo(ws, { type: 'left_room' });

    if (remaining === 0 && room.state === 'lobby') {
      this.rooms.delete(client.roomId);
      clearInterval(room.tickTimer);
    }
  }

  handleStartGame(ws) {
    const client = this.clients.get(ws);
    if (!client || !client.roomId) return;
    const room = this.rooms.get(client.roomId);
    if (!room) return;
    if (client.id !== room.hostId) { this.sendTo(ws, { type: 'error', message: '只有房主可以开始游戏' }); return; }
    room.startGame();
  }

  handleInput(ws, msg) {
    const client = this.clients.get(ws);
    if (!client || !client.roomId) return;
    const room = this.rooms.get(client.roomId);
    if (!room || room.state !== 'playing') return;
    // 客户端发送鼠标在世界中的位置, 需要转换为相对于玩家的方向
    const p = room.gamePlayers ? room.gamePlayers.get(client.id) : null;
    if (!p || !p.alive) return;
    const mouseWorldX = msg.mouseWorldX || p.x;
    const mouseWorldY = msg.mouseWorldY || p.y;
    room.setPlayerInput(client.id, {
      keys: msg.keys || {},
      mouseX: mouseWorldX - p.x,
      mouseY: mouseWorldY - p.y,
      shooting: !!msg.shooting,
      reloading: !!msg.reloading
    });
  }

  handleReady(ws) {
    const client = this.clients.get(ws);
    if (!client || !client.roomId) return;
    const room = this.rooms.get(client.roomId);
    if (!room) return;
    const player = room.humans.get(client.id);
    if (player) { player.ready = !player.ready; room.broadcast({ type: 'room_update', room: room.getLobbyData() }); }
  }

  handleSetMode(ws, mode) {
    const client = this.clients.get(ws);
    if (!client || !client.roomId) return;
    const room = this.rooms.get(client.roomId);
    if (!room || client.id !== room.hostId) return;
    if (room.state !== 'lobby') return;
    if (mode === MODE_DM || mode === MODE_5V5) {
      room.setGameMode(mode);
    }
  }

  handleAssignTeam(ws, team) {
    const client = this.clients.get(ws);
    if (!client || !client.roomId) return;
    const room = this.rooms.get(client.roomId);
    if (!room || room.gameMode !== MODE_5V5) return;
    if (team !== TEAM_BLUE && team !== TEAM_RED) return;
    room.assignTeam(client.id, team);
  }

  quickMatch5v5(ws) {
    const client = this.clients.get(ws);
    if (!client || client.roomId) return;
    for (const [id, room] of this.rooms) {
      if (room.state === 'lobby' && room.gameMode === MODE_5V5 && room.humans.size < TOTAL_SLOTS_5V5) {
        this.joinRoom(ws, id);
        return;
      }
    }
    this.createRoom(ws, '5v5对战 #' + generateId(4));
    const room = this.rooms.get(client.roomId);
    if (room) room.setGameMode(MODE_5V5);
  }

  handleDisconnect(ws) {
    const client = this.clients.get(ws);
    if (!client) return;
    if (client.roomId) this.leaveRoom(ws);
    this.matchmakingQueue = this.matchmakingQueue.filter(c => c !== ws);
    this.clients.delete(ws);
  }

  sendRoomList(ws) {
    const rooms = [];
    for (const [id, room] of this.rooms) {
      if (room.state === 'lobby') rooms.push(room.getInfo());
    }
    this.sendTo(ws, { type: 'room_list', rooms });
  }

  sendTo(ws, msg) {
    if (ws.readyState === 1) ws.send(JSON.stringify(msg));
  }
}

// ==================== 服务启动 ====================
const app = express();
const server = http.createServer(app);
const wss = new WebSocketServer({ server });
const gameServer = new GameServer();

app.use(express.static(path.join(__dirname, 'public')));

wss.on('connection', (ws) => gameServer.handleConnection(ws));

const PORT = process.env.PORT || 3000;
server.listen(PORT, '0.0.0.0', () => {
  console.log(`小人射击服务器已启动: http://0.0.0.0:${PORT}`);
  console.log('房间系统: 创建/加入/快速匹配');
  console.log('自动瞄准: 开火时自动锁定最近目标');
  console.log(`AI补齐: 不足${MAX_PLAYERS}人时自动填充机器人`);
});
