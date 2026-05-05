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
    this.state = 'lobby'; // lobby | countdown | playing | finished
    this.humans = new Map(); // playerId → { id, ws, name, color, ready }
    this.bots = [];
    this.bullets = [];
    this.pickups = [];
    this.particles = []; // for death effects
    this.tickTimer = null; this.tickNumber = 0;
    this.countdownTimer = null; this.countdownValue = 0;
    this.aliveCount = 0; this.gameTime = 0;
    this.killFeed = [];
    this.playerInputs = new Map(); // playerId → { keys, mouseX, mouseY, shooting, reloading }
    this.lastInputTime = new Map();
    this.lobbyBots = 0;         // 大厅中的人机占位数
    this.autoFillTimer = null;  // 自动填充定时器
    this.startAutoFill();
  }

  addHuman(clientId, ws, name) {
    const color = PLAYER_COLORS[this.humans.size % PLAYER_COLORS.length];
    const player = { id: clientId, ws, name, color, ready: true };
    this.humans.set(clientId, player);
    this.playerInputs.set(clientId, { keys: {}, mouseX: 0, mouseY: 0, shooting: false, reloading: false });
    this.lastInputTime.set(clientId, Date.now());
    // 真人加入时挤掉一个人机占位
    if (this.lobbyBots > 0 && (this.humans.size + this.lobbyBots) > MAX_PLAYERS) {
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
      if (this.humans.size + this.lobbyBots >= MAX_PLAYERS) {
        clearInterval(this.autoFillTimer); this.autoFillTimer = null;
        return;
      }
      this.lobbyBots++;
      this.broadcastLobby();
      if (this.humans.size + this.lobbyBots >= MAX_PLAYERS) {
        clearInterval(this.autoFillTimer); this.autoFillTimer = null;
        // 满员自动开局
        setTimeout(() => {
          if (this.state === 'lobby' && this.humans.size + this.lobbyBots >= MAX_PLAYERS) {
            this.startGame();
          }
        }, 500);
      }
    }, 1000);
  }

  stopAutoFill() {
    if (this.autoFillTimer) { clearInterval(this.autoFillTimer); this.autoFillTimer = null; }
  }

  restartAutoFill() {
    this.stopAutoFill();
    if (this.state === 'lobby' && this.humans.size + this.lobbyBots < MAX_PLAYERS) {
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
    this.state = 'playing'; this.bullets = []; this.particles = [];
    this.gameTime = 0; this.tickNumber = 0; this.killFeed = [];
    this.stopAutoFill();
    const spawns = getAmmoSpawns();
    this.pickups = spawns.map(s => ({ x: s.x, y: s.y, active: true, respawnTimer: 0 }));

    // 剩余空位全部用真实AI补齐到5人
    const humanCount = this.humans.size;
    const botsNeeded = MAX_PLAYERS - humanCount;
    this.bots = [];
    for (let i = 0; i < botsNeeded; i++) {
      const sp = SPAWN_POINTS[humanCount + i] || SPAWN_POINTS[4];
      this.bots.push(new BotAI('bot_' + this.id + '_' + i,
        sp.x + (Math.random() - 0.5) * 60, sp.y + (Math.random() - 0.5) * 60,
        BOT_COLORS[i % BOT_COLORS.length], BOT_NAMES[i % BOT_NAMES.length]));
    }
    this.lobbyBots = 0;

    this.gamePlayers = new Map();
    let si = 0;
    for (const [id, h] of this.humans) {
      const sp = SPAWN_POINTS[si] || SPAWN_POINTS[4];
      this.gamePlayers.set(id, {
        id, x: sp.x, y: sp.y, angle: 0, hp: MAX_HP, mag: MAG_SIZE, reserve: RESERVE_MAX,
        reloading: false, reloadTimer: 0, fireCooldown: 0, alive: true,
        name: h.name, color: h.color, isBot: false, vx: 0, vy: 0, speed: PLAYER_SPEED
      });
      si++;
    }

    this.aliveCount = humanCount + this.bots.length;

    const mapData = MAP_DATA;
    this.broadcast({
      type: 'game_start',
      map: mapData,
      tileSize: TILE,
      mapW: MAP_W,
      mapH: MAP_H,
      worldW: WORLD_W,
      worldH: WORLD_H,
      yourId: null // will be set per-client below
    });

    // Send personalized game_start to each human
    for (const [id, h] of this.humans) {
      this.sendTo(h.ws, {
        type: 'game_start',
        map: mapData, tileSize: TILE, mapW: MAP_W, mapH: MAP_H,
        worldW: WORLD_W, worldH: WORLD_H,
        yourId: id
      });
    }

    this.tickTimer = setInterval(() => this.tick(), TICK_RATE);
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
    return {
      id: this.id, name: this.name,
      playerCount: this.humans.size + this.lobbyBots,
      maxPlayers: MAX_PLAYERS,
      state: this.state,
      hostId: this.hostId
    };
  }

  getLobbyData() {
    const players = [];
    for (const [id, h] of this.humans) players.push({ id, name: h.name, isHost: id === this.hostId });
    // 人机占位
    for (let i = 0; i < this.lobbyBots; i++) {
      players.push({ id: 'bot_ph_' + i, name: '人机 ' + (i + 1), isHost: false, isBot: true });
    }
    return { id: this.id, name: this.name, players, hostId: this.hostId, state: this.state, maxPlayers: MAX_PLAYERS, lobbyBots: this.lobbyBots };
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

    ws.on('message', (raw) => {
      try {
        const msg = JSON.parse(raw.toString());
        this.handleMessage(ws, msg);
      } catch (e) { this.sendTo(ws, { type: 'error', message: '消息格式错误' }); }
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

      default:
        break;
    }
  }

  createRoom(ws, roomName) {
    const client = this.clients.get(ws);
    if (!client) return;
    if (client.roomId) { this.sendTo(ws, { type: 'error', message: '已在房间中' }); return; }

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
    if (room.humans.size >= MAX_PLAYERS) { this.sendTo(ws, { type: 'error', message: '房间已满' }); return; }

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
      if (room.state === 'lobby' && room.humans.size < MAX_PLAYERS) {
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
