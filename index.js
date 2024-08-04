const mineflayer = require('mineflayer');
const readline = require('readline');
const process = require('process');
const rl = readline.createInterface({
  input: process.stdin,
  output: process.stdout,
});
const { once } = require('events');
const registry = require('prismarine-registry')('1.8.9');
const ChatMessage = require('prismarine-chat')(registry);
const { check, Window } = require('./window.js');
const utils = require(`./utils.js`);
const { randomUUID } = require('crypto');
const axios = require('axios');
const stateManger = require(`./state.js`);
const { noColorCodes, nicerFinders, normalizeDate, IHATETAXES, formatNumber, sleep, getWindowName, getPurse, relistCheck, addCommasToNumber } = require('./utils.js');
const { Webhook, MessageBuilder } = require('discord-webhook-node');
const { getPackets, makePackets } = require('./packetStuff.js');
const { silly, debug, error, info, logmc } = require('./logger.js');
const { startWS, send, handleCommand, ws, sidListener, solveCaptcha } = require('./websocketHelper.js');
const { config, updateConfig } = require('./config.js');
const nbt = require('prismarine-nbt');
const fastJsonParse = require('fast-json-parse');

let ign, bedSpam, discordid, TOS, webhook, usInstance, clickDelay, delay, usingBaf, session, discordbot, badFinders, waittime;
let lastGui = 0;
let targetQueue = [], idQueue = [], finderQueue = [], purchasedIds = [], purchasedTargets = [], purchasedFinders = [];
let lastOpenedAhids = [], lastOpenedTargets = [], lastOpenedFinders = [], lastListedIds = [], lastListedTargets = [];
let ranit = false, totalslots = 17, currentlisted = 0, closedGui = false, bedFailed = false;
let bot, cdClaim = 0, fullInv = false, relistClaim = false, uuidFound = false, lastLeftBuying;
let lastAction = Date.now();
let privacySettings;

const relistObjectMap = new Map();
const webhookPricingMap = new Map();

const cache = new Map();
const memoize = (fn) => {
  return (...args) => {
    const key = JSON.stringify(args);
    if (cache.has(key)) return cache.get(key);
    const result = fn(...args);
    cache.set(key, result);
    return result;
  };
};

function initConfig() {
  ign = config.username;
  webhook = config.webhook;
  TOS = config.TOS;
  session = config.session;
  bedSpam = config.bedSpam;
  discordid = config.discordID;
  discordbot = config.discordBotToken;
  delay = config.delay;
  clickDelay = config.clickDelay;
  waittime = config.waittime;
  usingBaf = config.useBafSocket;
  usInstance = config.usInstance;
  percentOfTarget = config.percentOfTarget;
  relist = config.relist;
  ownAuctions = config.ownAuctions;
  badFinders = config.doNotListFinders ? config.doNotListFinders : ['USER'];

  if (webhook) {
    webhook = new Webhook(webhook);
    webhook.setUsername('TPM');
    webhook.setAvatar('https://media.discordapp.net/attachments/1235761441986969681/1263290313246773311/latest.png?ex=6699b249&is=669860c9&hm=87264b7ddf4acece9663ce4940a05735aecd8697adf1335de8e4f2dda3dbbf07&=&format=webp&quality=lossless');
  }

  if (!session) {
    session = randomUUID();
    config.session = session;
    updateConfig(config);
    sidListener(session);
  }

  startWS(session);
  lastAction = Date.now();
}

const getReadyMemoized = memoize(async function getReady() {
  ranit = true;
  await sleep(5000);
  bot.chat("/sbmenu");
  debug("sbmenu opened");
  return new Promise((resolve) => {
    bot.once('windowOpen', async (window) => {
      if (bot.currentWindow.title.includes("SkyBlock Menu") && bot.currentWindow.slots[48].nbt.value.display.value.Name.value.includes("Profile Management")) {
        bot.currentWindow.requiresConfirmation = false;
        bot.clickWindow(48, 0, 0);
        debug("profile management opened");
        bot.once('windowOpen', async (window) => {
          if (bot.currentWindow.title.includes("Profile Management")) {
            for (const item of bot.currentWindow.slots) {
              if (!item || item.slot <= 9 || item.slot >= 17) continue;
              if (item.displayName === "Block of Emerald") {
                const itemNbt = nbt.simplify(item.nbt);
                const coop = itemNbt.display.Lore.find(line => line.includes("Co-op with"))?.replace(/§./g, "");
                if (coop) {
                  const coopRegexPlayers = /Co-op with (\d+) players:/;
                  const coopRegexSinglePlayer = /Co-op with (?:\[.*\]\s*)?([\w]+)/;
                  const matchPlayers = coop.match(coopRegexPlayers);
                  if (matchPlayers) {
                    const numberOfPlayers = parseInt(matchPlayers[1], 10);
                    totalslots = 14 + (numberOfPlayers * 3);
                  } else {
                    const matchSinglePlayer = coop.match(coopRegexSinglePlayer);
                    if (matchSinglePlayer) {
                      totalslots = 17;
                    } else {
                      error("Unrecognized COOP format:", coop);
                    }
                  }
                } else {
                  totalslots = 14;
                }
                await sleep(500);
                bot.chat('/ah');
                await once(bot, 'windowOpen');
                if ((getWindowName(bot.currentWindow)?.includes("Co-op Auction House") || getWindowName(bot.currentWindow)?.includes("Auction House")) &&
                    (bot.currentWindow.slots[15].nbt.value.display.value.Name.value?.includes("Manage Auctions") || 
                     bot.currentWindow.slots[15].nbt.value.display.value.Name.value?.includes("Create Auction"))) {
                  const item = bot.currentWindow.slots[15];
                  if (item) {
                    const itemNbt = nbt.simplify(item.nbt);
                    const cleanedLoreLines = itemNbt.display?.Lore?.map(line => line.replace(/§./g, "")) || [];
                    const none = cleanedLoreLines.find(line => line.includes("Set your own items"));
                    const one = cleanedLoreLines.find(line => line.includes("You own 1 auction"));
                    const multiple = cleanedLoreLines.find(line => /You own \d+ auctions/.test(line));
                    if (none) currentlisted = 0;
                    if (one) currentlisted = 1;
                    if (multiple) {
                      const match = multiple.match(/You own (\d+) auctions in/);
                      if (match && match[1]) currentlisted = parseInt(match[1], 10);
                    }
                    await sleep(500);
                    const toclaim1 = cleanedLoreLines.find(line => line.includes("Your auctions have 1 bid"));
                    const toclaim2 = cleanedLoreLines.find(line => /Your auctions have \d+ bids/.test(line));
                    if (toclaim1) {
                      await sleep(500);
                      bot.currentWindow.requiresConfirmation = false;
                      bot.clickWindow(15, 0, 0);
                      await once(bot, 'windowOpen');
                      await sleep(500);
                      bot.currentWindow.requiresConfirmation = false;
                      bot.clickWindow(10, 0, 0);
                      await once(bot, 'windowOpen');
                      await sleep(500);
                      bot.currentWindow.requiresConfirmation = false;
                      bot.clickWindow(31, 0, 0);
                      currentlisted--;
                    }
                    if (toclaim2) {
                      const match = toclaim2.match(/Your auctions have (\d+) bids/);
                      const bids = match && match[1] ? parseInt(match[1], 10) : 0;
                      await sleep(500);
                      bot.currentWindow.requiresConfirmation = false;
                      bot.clickWindow(15, 0, 0);
                      await once(bot, 'windowOpen');
                      await sleep(500);
                      const slotsToCheck = [...Array(51).keys()];
                      slotsToCheck.forEach(slot => {
                        const item = bot.currentWindow.slots[slot];
                        if (item && item.nbt && item.nbt.value.display && item.nbt.value.display.value.Name) {
                          const itemName = item.nbt.value.display.value.Name.value;
                          if (!config.ownAuctions && itemName.includes("Claim All")) {
                            bot.currentWindow.requiresConfirmation = false;
                            bot.clickWindow(slot, 0, 0);
                          } else if (config.ownAuctions && itemName.includes("Claim Your")) {
                            bot.currentWindow.requiresConfirmation = false;
                            bot.clickWindow(slot, 0, 0);
                          }
                        }
                      });
                      currentlisted -= bids;
                    }
                    if (!toclaim1 && !toclaim2 && bot.currentWindow) bot.closeWindow(bot.currentWindow);
                  }
                }
                resolve("ready to start flipping, connecting to socket");
                return;
              }
            }
          }
        });
      }
    });
  });

});

async function relistHandler(purchasedAhids, purchasedPrices) {
  bot.state = "listing";
  relistClaim = false;
  let itemuuid;
  const idToRelist = purchasedAhids;
  const priceToRelist = purchasedPrices;
  debug("Starting relist process for item with ahid:", idToRelist, "and target:", priceToRelist, 'bot state:', bot.state);
  bot.chat(`/viewauction ${idToRelist}`);
  await once(bot, 'windowOpen');
  if (getWindowName(bot.currentWindow)?.includes("BIN Auction View")) {
    await sleep(500);
    try {
      itemuuid = nbt.simplify(bot.currentWindow?.slots[13]?.nbt)?.ExtraAttributes?.uuid;
    } catch (e) {
      error(`[TPM] Error getting item UUID, leaving listing`);
      bot.state = null;
      if (bot.currentWindow) bot.closeWindow(bot.currentWindow);
      return;
    }
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(31, 0, 0);
    await sleep(500);
    if (cdClaim > 0 && bot.currentWindow) {
      bot.currentWindow.requiresConfirmation = false;
      bot.clickWindow(31, 0, 0);
      await sleep(200);
      if (!relistClaim) {
        logmc("§6[§bTPM§6] §cAborting relist after 2 failed item claim attempts");
        purchasedAhids.unshift(idToRelist);
        purchasedPrices.unshift(priceToRelist);
        stateManger.add({ id: purchasedAhids, targets: purchasedPrices }, Infinity, 'listing');
        bot.state = null;
        cdClaim = 0;
        return;
      }
    }
    if (fullInv && bot.currentWindow) {
      bot.currentWindow.requiresConfirmation = false;
      bot.clickWindow(31, 0, 0);
      await sleep(200);
      logmc("§6[§bTPM§6] §cAborting relist because of full inventory (unable to claim item for relist)");
      if (webhook) {
        const embed = new MessageBuilder()
          .setFooter(`The "Perfect" Macro`, 'https://media.discordapp.net/attachments/1223361756383154347/1263302280623427604/capybara-square-1.png?ex=6699bd6e&is=66986bee&hm=d18d0749db4fc3199c20ff973c25ac7fd3ecf5263b972cc0bafea38788cef9f3&=&format=webp&quality=lossless&width=437&height=437')
          .setTitle('Inventory Full')
          .addField('', `Unable to claim item for relist due to full inventory. Please log on and clear space in inventory to continue auto relisting (:`)
          .setThumbnail(`https://mc-heads.net/head/${config.uuid}.png`)
          .setColor(2615974);
        webhook.send(embed);
      }
      bot.state = null;
      return;
    }
  }
  debug("opening /ah");
  bot.chat("/ah");
  await once(bot, 'windowOpen');
  if (!bot.currentWindow) {
    logmc("§6[§bTPM§6] §cWas not able to open AH to sell item, trying again");
    await sleep(200);
    bot.chat("/ah");
    await once(bot, 'windowOpen');
    if (!bot.currentWindow) {
      logmc("§6[§bTPM§6] §cFailed again, aborting!!!");
      bot.state = null;
      lastAction = Date.now();
      return;
    }
  }
  for (const item of bot.currentWindow.slots) {
    if (!item) continue;
    if (nbt.simplify(item?.nbt)?.ExtraAttributes?.uuid === itemuuid) {
      debug("found item in inventory to relist with uuid", itemuuid);
      uuidFound = true;
      bot.currentWindow.requiresConfirmation = false;
      await sleep(200);
      bot.clickWindow(item.slot, 0, 0);
      debug("added item into ah menu");
      break;
    }
  }
  if (!uuidFound) {
    logmc("§6[§bTPM§6] §cItem not found in inventory please report this (: Aborting relist process for this item ):");
    if (bot.currentWindow) bot.closeWindow(bot.currentWindow);
    await sleep(250);
    bot.state = null;
    logmc("§6[§bTPM§6] §3Hopefully exited annoying bug safely (if not report this)");
    return;
  }
  uuidFound = false;
  await once(bot, 'windowOpen');
  if ((getWindowName(bot.currentWindow)?.includes("Create BIN Auction")) && bot.currentWindow.slots[33].nbt.value.display.value.Name.value?.includes("6 Hours")) {
    debug("Auction Duration Menu Opened");
    await sleep(200);
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(33, 0, 0);
  } else if (!getWindowName(bot.currentWindow)?.includes('Create BIN Auction')) {
    logmc("§6[§bTPM§6] §cItem probably already in slot, please remove it :) Aborting relist process for this item ):");
    if (bot.currentWindow) bot.closeWindow(bot.currentWindow);
    await sleep(250);
    bot.state = null;
    logmc("§6[§bTPM§6] §3Hopefully exited annoying bug safely (if not report this)");
    return;
  }
  await once(bot, 'windowOpen');
  if (bot.currentWindow?.title?.includes("Auction Duration")) {
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(14, 0, 0);
    debug("Auction Duration set to 2 days");
  }
  await once(bot, 'windowOpen');
  if ((getWindowName(bot.currentWindow)?.includes("Create BIN Auction")) && bot.currentWindow.slots[33].nbt.value.display.value.Name.value?.includes("2 Days")) {
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(31, 0, 0);
    debug("opened bid creation menu");
  }
  await sleep(500);
  debug("PRICEHERE " + priceToRelist);
  let listpriceomg = priceToRelist;
  let relistpercent = 100;
  for (let i = 0; i < percentOfTarget.length; i += 3) {
    let lowerBound = percentOfTarget[i];
    let upperBound = percentOfTarget[i + 1];
    let percent = percentOfTarget[i + 2];
    if (priceToRelist >= lowerBound && priceToRelist < upperBound) {
      relistpercent = percent;
      break;
    }
  }
  debug("lpomg " + listpriceomg);
  debug("relistpercent", relistpercent);
  let result = priceToRelist * (relistpercent / 100);
  result = Math.round(result);
  debug("result", result);
  let strResult = result.toString();
  if (strResult.length > 3) {
    let firstThreeDigits = strResult.substring(0, 3);
    let remainingZeros = '0'.repeat(strResult.length - 3);
    listpriceomg = Number(firstThreeDigits + remainingZeros);
  } else {
    listpriceomg = result;
  }
  debug("listprice is", listpriceomg);
  bot._client.write('update_sign', {
    location: bot.entity.position.offset(-1, 0, 0),
    text1: `\"${listpriceomg.toString()}\"`,
    text2: '{"italic":false,"extra":["^^^^^^^^^^^^^^^"],"text":""}',
    text3: '{"italic":false,"extra":["Your auction"],"text":""}',
    text4: '{"italic":false,"extra":["starting bid"],"text":""}'
  });
  debug("set list price to", listpriceomg);
  await sleep(500);
  debug("AAAAAAAAAAAAA", bot.currentWindow.slots[31].nbt.value.display.value.Name.value);
  debug("Listed price", listpriceomg);
  let numWithCommas = addCommasToNumber(listpriceomg);
  debug(numWithCommas);
  await sleep(500);
  debug("Debug time:", getWindowName(bot.currentWindow), bot.currentWindow.slots[31].nbt.value.display.value.Name.value, bot.currentWindow.slots[33].nbt.value.display.value.Name.value);
  if (getWindowName(bot.currentWindow)?.includes("Create BIN Auction") && bot.currentWindow.slots[31].nbt.value.display.value.Name.value?.includes(`${numWithCommas} coins`) && bot.currentWindow.slots[33].nbt.value.display.value.Name.value?.includes("2 Days")) {
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(29, 0, 0);
    debug("bid confirmed, finalizing auction listing");
    lastListedIds.push(idToRelist);
    lastListedTargets.push(listpriceomg);
  }
  await once(bot, 'windowOpen');
  if (bot.currentWindow.title.includes("Confirm BIN Auction")) {
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(11, 0, 0);
    await once(bot, 'windowOpen');
    if (bot.currentWindow.slots[29]?.type == 394 && (getWindowName(bot.currentWindow)?.includes("BIN Auction View"))) {
      logmc("§6[§bTPM§6] §3Auction listed :D");
      bot.closeWindow(bot.currentWindow);
      bot.state = null;
      lastAction = Date.now();
      currentlisted++;
      debug(`Current listed: ${currentlisted}`);
    }
  }
}

async function start() {
  initConfig();
  bot = mineflayer.createBot({
    username: ign,
    auth: 'microsoft',
    logErrors: true,
    version: '1.8.9',
    host: 'play.hypixel.net',
  });
  await makePackets(bot._client);
  const packets = getPackets();

  bot.once('login', () => {
    if (!config.uuid) {
      axios.get(`https://api.mojang.com/users/profiles/minecraft/${bot.username}`)
        .then(response => {
          config.uuid = response.data.id;
          updateConfig(config);
        })
        .catch(error => console.error(`Error fetching UUID for ign ${bot.username}:`, error));
    }
  });

  bot.state = 'moving';
  let firstGui;

  Window.on('newWindow', async window => {
    bot.currentWindow.requiresConfirmation = false;
    const name = getWindowName(window);
    lastGui = Date.now();
    if (name === 'BIN Auction View' && bot.state !== 'listing') {
      debug("bot state", bot.state);
      bot.clickWindow(31, 0, 0);
      lastLeftBuying = Date.now();
      bot.state = 'buying';
      firstGui = lastGui;
      await sleep(6);
      const item = bot.currentWindow?.slots[31]?.name;
      switch (item) {
        case 'poisonous_potato':
        case 'potato':
        case 'feather':
          bot.closeWindow(bot.currentWindow);
          bot.state = null;
          break;
        case 'gold_block':
          bot.state = null;
          break;
      }
    } else if (name === 'Confirm Purchase') {
      bot.clickWindow(11, 0, 0);
      logmc(`§6[§bTPM§6] §3Confirm at ${Date.now() - firstGui}ms`);
      if (bedSpam || bedFailed) {
        for (let i = 1; i < 11; i++) {
          await sleep(30);
          if (getWindowName(bot.currentWindow)) {
            bot.clickWindow(11, 0, 0);
          } else {
            break;
          }
        }
      }
      bot.state = null;
    }
  });

  setInterval(() => check(bot), 1);

  setInterval(async () => {
    if (bot.state === 'buying' && Date.now() - lastLeftBuying > 5000) {
      error("Bot state issue detected, resetting state and hopefully fixing queue lock issue");
      if (bot.currentWindow) bot.closeWindow(bot.currentWindow);
      await sleep(200);
      bot.state = null;
    }
  }, 250);

  let old = bot.state;
  setInterval(async () => {
    const current = stateManger.get();
    if (bot.state !== old) debug(`Bot state updated: ${bot.state}`);
    old = bot.state;
    if (current && bot.state === null && Date.now() - lastAction > delay) {
      const command = current.command;
      if (command === 'claim') {
        bot.state = current.state;
        bot.state = 'claiming';
        await claimBought();
        bot.state = null;
      } else if (command === 'sold') {
        bot.state = current.state;
        bot.state = 'claiming';
        await claimSold();
        bot.state = null;
      } else if (command?.id) {
        if(currentlisted == totalslots){
          debug(`AH full, not listing from queue`);
          return;
        }
        if (fullInv) {
          logmc("§6[§bTPM§6] §cNot attempting to relist because your inventory is full. You will need to log in and clear your inventory to continue");
          bot.state = null;
        } else {
          await sleep(10000);
          if (relistCheck(currentlisted, totalslots, bot.state)) {
            bot.state = "listing";
            await sleep(500);
            relistHandler(command.id, command.targets);
          } else {
            stateManger.add(command, Infinity, 'listing');
          }
        }
      } else {
        bot.state = current.state;
        const ahhhhh = webhookPricingMap.get(command);
        if (ahhhhh) {
          var ahid = ahhhhh.id;
        } else {
          error(`Ahhh didn't find ${command} in webhookPricingMap`);
        }
        bedFailed = true;
        currentOpen = ahid;
        bot.chat(`/viewauction ${ahid}`);
      }
      stateManger.next();
      lastAction = Date.now();
      debug(`Turning state into ${bot.state} and running ${current.command}`);
    }
  }, 1);

  bot.once('spawn', async () => {
    await bot.waitForChunksToLoad();
    await sleep(5000);
    bot.state = 'moving';
    bot.chat('/play sb');
    await sleep(5000);
    bot.chat('/is');
    setInterval(() => {
      const board = bot.scoreboard?.sidebar?.items;
      if (!board) {
        bot.chat('/l');
        return;
      }
      let scoreboard = bot.scoreboard.sidebar.items.map(item => item.displayName.getText(null).replace(item.name, ''));
      scoreboard.forEach(async line => {
        if (line.includes('Village')) {
          bot.state = 'moving';
          logmc('§6[§bTPM§6] §cBot found in the hub :( going back to skyblock');
          bot.chat('/is');
          lastAction = Date.now();
        }
        if (line.includes('Rank:') || line.includes('bugs')) {
          bot.state = 'moving';
          logmc('§6[§bTPM§6] §cBot found in the lobby :( going back to skyblock');
          bot.chat('/play sb');
          lastAction = Date.now();
        }
        if (line.includes('Your Island')) {
          if (!ranit) {
            getReadyMemoized();
          } else {
            if (bot.state === 'moving') bot.state = null;
            lastAction = Date.now();
          }
        }
      });
    }, 30000);
  });

  bot.on('error', e => error(e));

  bot.on('login', () => bot.chat('/locraw'));

  bot.on('message', async (message, type) => {
    let text = message.getText(null);
    const msg = new ChatMessage(message);
    if (type === 'chat') {
      logmc(message.toAnsi());
    }
    switch (text) {
      case 'Putting coins in escrow...':
        logmc(`§6[§bTPM§6] §3Auction bought in ${Date.now() - firstGui}ms`);
        bot.state = null;
        if (bot.currentWindow && !closedGui) bot.closeWindow(bot.currentWindow);
        closedGui = true;
        break;
      case "This auction wasn't found!":
      case "The auctioneer has closed this auction!":
      case "You don't have enough coins to afford this bid!":
        bot.state = null;
        if (bot.currentWindow && !closedGui) bot.closeWindow(bot.currentWindow);
        closedGui = true;
        break;
      case '/limbo for more information.':
        await sleep(5000);
        bot.state = 'moving';
        bot.chat('/lobby');
        break;
      case 'You may only use this command after 4s on the server!':
      case "You didn't participate in this auction!":
        bot.state = null;
        break;
      case "Claiming this auction is on cooldown!":
        cdClaim++;
        break;
      case "There isn't enough space in your inventory!":
        fullInv = true;
        break;
    }

    if (/You claimed (.+?) from (?:\[.*?\] )?(.+?)'s auction!/.test(text) && config.relist) {
      relistClaim = true;
    }

    const regex = /BIN Auction started for (.+?)!/;
    const match33 = text.match(regex);
    if (match33) {
      const item = match33[1];
      const auctionUrl = `https://sky.coflnet.com/auction/${lastListedIds.shift()}`;
      const purse = formatNumber(await getPurse(bot));
      if (webhook) {
        const embed = new MessageBuilder()
          .setFooter(`The "Perfect" Macro - Purse: ${purse}`, 'https://media.discordapp.net/attachments/1223361756383154347/1263302280623427604/capybara-square-1.png?ex=6699bd6e&is=66986bee&hm=d18d0749db4fc3199c20ff973c25ac7fd3ecf5263b972cc0bafea38788cef9f3&=&format=webp&quality=lossless&width=437&height=437')
          .setTitle('Item listed')
          .addField('', `Listed \`${item}\` for \`${addCommasToNumber(lastListedTargets.shift())} coins\` [click](${auctionUrl}) \n [AH Slots: ${currentlisted}/${totalslots}]`)
          .setThumbnail(`https://mc-heads.net/head/${config.uuid}.png`)
          .setColor(13677311);
        webhook.send(embed);
      }
      sendScoreboard();
    }

    const regex1 = /You purchased (.+?) for ([\d,]+) coins!/;
    const match1 = text.match(regex1);
    if (match1) {
      let lastPurchasedAhid;
      let lastPurchasedTarget;
      let lastPurchasedFinder;
      const item = utils.noColorCodes(match1[1]).replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, "");
      const object = relistObjectMap.get(item);
      if (lastOpenedAhids.length > 0 && config.relist) {
        if (object) {
          lastPurchasedAhid = object.id;
          lastPurchasedTarget = object.target;
          lastPurchasedFinder = object.finder;
          if (!badFinders?.includes(lastPurchasedFinder)) {
            purchasedFinders.push(lastPurchasedFinder);
            setTimeout(async () => {
              if (bot.state === null) {
                if (fullInv) {
                  logmc("§6[§bTPM§6] §cNot attempting to relist because your inventory is full. You will need to log in and clear your inventory to continue");
                  bot.state = null;
                } else {
                  if (relistCheck(currentlisted, totalslots, bot.state)) {
                    bot.state = "listing";
                    await sleep(500);
                    relistHandler(lastPurchasedAhid, lastPurchasedTarget);
                  } else {
                    debug(`relist check didn't work`);
                    stateManger.add({ id: lastPurchasedAhid, targets: lastPurchasedTarget }, Infinity, 'listing');
                    bot.state = null;
                  }
                }
              } else {
                debug(`bot state check didn't work`);
                stateManger.add({ id: lastPurchasedAhid, targets: lastPurchasedTarget }, Infinity, 'listing');
                bot.state = null;
              }
            }, 10000);
          } else {
            logmc(`§6[§bTPM§6] §cUser finder flip found, not relisting ${lastPurchasedFinder}`);
          }
        } else {
          error(`Didn't find ${item} in relistObjectMap. Please report this to icyhenryt`);
        }
      }
      if (bot.state == 'buying') bot.state = null;
      const price = match1[2];
      const webhookPricingItem = webhookPricingMap.get(item);
      if (!webhookPricingItem) {
        error(`Didn't find ${item} in webhookPricingMap. Please report this to icyhenryt`);
        return;
      }
      const itemBed = webhookPricingItem.bed;
      const auctionUrl = `https://sky.coflnet.com/auction/${webhookPricingItem.auctionId}`;
      const profit = utils.IHATETAXES(webhookPricingItem.target) - utils.onlyNumbers(price);
      const purse = utils.formatNumber(await getPurse(bot) - parseInt(String(price).replace(/,/g, ''), 10));
      if (webhook) {
        const embed = new MessageBuilder()
          .setFooter(`TPM - Found by ${nicerFinders(webhookPricingItem.finder)} - Purse: ${purse} `, 'https://media.discordapp.net/attachments/1223361756383154347/1263302280623427604/capybara-square-1.png?ex=6699bd6e&is=66986bee&hm=d18d0749db4fc3199c20ff973c25ac7fd3ecf5263b972cc0bafea38788cef9f3&=&format=webp&quality=lossless&width=437&height=437')
          .setTitle('Item purchased')
          .addField('', `Bought \`${utils.noColorCodes(match1[1])}\` for \`${price} coins\` (\`${utils.formatNumber(profit)}\` profit) [click](${auctionUrl}) ${itemBed}`)
          .setThumbnail(`https://mc-heads.net/head/${config.uuid}.png`)
          .setColor(2615974);
        webhook.send(embed);
      }
      sendScoreboard();
      if (!config.relist) {
        setTimeout(async () => {
          if (bot.state === null) {
            bot.state = 'claiming';
            await claimBought();
            bot.state = null;
          } else {
            stateManger.add('claim', 37, 'claiming');
          }
        }, 500);
      }
    }
    const regex2 = /\[Auction\] (.+?) bought (.+?) for ([\d,]+) coins CLICK/;
    const match2 = text.match(regex2);
    if (match2) {
      const buyer = match2[1];
      const item = match2[2];
      const price = utils.onlyNumbers(match2[3]);
      currentlisted--;
      if (webhook) {
        const purse = utils.formatNumber(await getPurse(bot) + parseInt(String(price).replace(/,/g, ''), 10));
        const embed = new MessageBuilder()
          .setFooter(`The "Perfect" Macro - Purse: ${purse} `, `https://media.discordapp.net/attachments/1223361756383154347/1263302280623427604/capybara-square-1.png?ex=6699bd6e&is=66986bee&hm=d18d0749db4fc3199c20ff973c25ac7fd3ecf5263b972cc0bafea38788cef9f3&=&format=webp&quality=lossless&width=437&height=437`)
          .setTitle('Item Sold')
          .addField('', `Collected \`${addCommasToNumber(price)} coins\` for selling \`${item}\` to \`${buyer}\``)
          .setThumbnail(`https://mc-heads.net/head/${config.uuid}.png`)
          .setColor(16731310);
        webhook.send(embed);
      }
      setTimeout(async () => {
        if (bot.state === null) {
          bot.state = 'claiming';
          await claimSold();
          bot.state = null;
          sendScoreboard();
        } else {
          stateManger.add('sold', 28, 'claiming');
        }
      }, 500);
    }
  });

  function askUser() {
    rl.question('> ', input => {
      const args = input.trim().split(/\s+/);
      switch (args[0]) {
        case 'chat':
          const message = args.slice(1).join(' ');
          packets.sendMessage(message);
          break;
        case '/cofl':
        case "/tpm":
        case '/icymacro':
          handleCommand(input);
          break;
        case '!c':
          solveCaptcha(args[1]);
          break;
      }
      askUser();
    });
  }
  askUser();

  async function claimBought() {
    bot.chat('/ah');
    await sleep(300);
    if (!bot.currentWindow) return;
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(13, 0, 0);
    await sleep(300);
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(10, 0, 0);
    await sleep(50);
  }

  async function claimSold() {
    bot.chat('/ah');
    await sleep(300);
    if (getWindowName(bot.currentWindow)?.includes('Auction House')) {
      bot.currentWindow.requiresConfirmation = false;
      bot.clickWindow(15, 0, 0);
      await sleep(300);
      if (getWindowName(bot.currentWindow)?.includes('Manage Auctions')) {
        bot.currentWindow.requiresConfirmation = false;
        const items = bot.currentWindow?.slots;
        items.forEach(async (item, index) => {
          if (!item) return;
          const name = item?.value?.display?.value?.Name?.value?.toString();
          if (name?.includes('Claim')) {
            bot.clickWindow(index, 0, 0);
            sleep(50);
            if (fullInv) {
              logmc("§6[§bTPM§6] §cNot attempting to relist because your inventory is full. You will need to log in and clear your inventory to continue");
              bot.state = null;
            } else {
              await sleep(5000);
              if (relistCheck(purchasedIds, currentlisted, totalslots, bot.state)) {
                bot.state = "listing";
                await sleep(500);
                relistHandler(purchasedIds, purchasedTargets);
              } else {
                stateManger.add({ id: purchasedIds, targets: purchasedTargets }, 4, 'listing');
              }
            }
            return;
          }
        });
        items.forEach((item, index) => {
          if (!item) return;
          const lore = item.nbt.value?.display?.value?.Lore?.value?.value?.toString();
          if (lore?.includes('Sold!')) {
            bot.clickWindow(index, 0, 0);
          }
        });
      } else {
        console.error(`Didn't properly claim sold auction not finding Manage auctions. Found ${getWindowName(bot.currentWindow)}`);
      }
    } else {
      console.error(`Didn't properly claim sold auction not finding Auction House. Found ${getWindowName(bot.currentWindow)}`);
    }
    return;
  }

  ws.on('flip', async msg => {
    let bed = '[NUGGET]';
    const data = fastJsonParse(msg.data).value;
    let itemName;
    let auctionID;
    let currentTime = Date.now();
    if (usingBaf) {
      if (!bot.state && currentTime - lastAction > delay) {
        lastLeftBuying = currentTime;
        bot.state = 'buying';
        auctionID = data.id;
        packets.sendMessage(`/viewauction ${auctionID}`);
        let target = data.target;
        let finder = data.finder;
        itemName = data.itemName.replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, "");
        lastAction = currentTime;
        logmc(`§6[§bTPM§6] §8Opening ${itemName}`);
        closedGui = false;
        bedFailed = false;
        currentOpen = data.id;
        lastOpenedTargets.length = 0;
        lastOpenedTargets.push(target);
        lastOpenedAhids.length = 0;
        lastOpenedAhids.push(auctionID);
        lastOpenedFinders.length = 0;
        lastOpenedFinders.push(finder);
        relistObjectMap.set(noColorCodes(itemName).replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, ""), {
          id: auctionID,
          target: target,
          finder: data.finder
        });
      } else {
        auctionID = data.id;
        itemName = data.itemName.replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, "");
        logmc(`§6[§bTPM§6] §aAdding ${itemName}§3 to the pipeline because state is ${bot.state}!`);
        stateManger.add(noColorCodes(itemName).replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, ""), 69, 'buying');
      }
      idQueue.push(data.id);
      targetQueue.push(data.target);
      finderQueue.push(data.finder);
      const ending = new Date(normalizeDate(data.purchaseAt)).getTime();
      webhookPricingMap.set(noColorCodes(itemName), {
        target: data.target,
        price: data.startingBid,
        auctionId: auctionID,
        bed: bed,
        finder: data.finder,
      });
      if (currentTime < ending) {
        bed = '[BED]';
        webhookPricingMap.get(noColorCodes(itemName).replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, "")).bed = bed;
        setTimeout(async () => {
          for (let i = 0; i < 4; i++) {
            if (getWindowName(bot.currentWindow)?.includes('BIN Auction View')) {
              bot.clickWindow(31, 0, 0);
              await sleep(3);
            }
          }
        }, ending - Date.now() - waittime);
        setTimeout(() => {
          if (getWindowName(bot.currentWindow)?.includes('BIN Auction View') && currentOpen === auctionID) {
            bot.closeWindow(bot.currentWindow);
            bot.state = null;
            logmc(`§6[§bTPM§6] §cBed timing failed and we had to abort the auction :( Please lower your waittime if this continues or turn on bedspam`);
          }
        }, 5000);
      }
    } else {
      if (!bot.state && currentTime - lastAction > delay) {
        auctionID = data.id;
        lastLeftBuying = Date.now();
        bot.state = 'buying';
        packets.sendMessage(`/viewauction ${auctionID}`);
        let target = data.target;
        let finder = data.finder;
        bedFailed = false;
        closedGui = false;
        itemName = data.auction.itemName;
        logmc(`§6[§bTPM§6] §8Opening ${itemName}`);
        lastAction = currentTime;
        currentOpen = auctionID;
        lastOpenedTargets.length = 0;
        lastOpenedTargets.push(target);
        lastOpenedAhids.length = 0;
        lastOpenedAhids.push(auctionID);
        lastOpenedFinders.length = 0;
        lastOpenedFinders.push(finder);
        relistObjectMap.set(noColorCodes(itemName).replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, ""), {
          id: auctionID,
          target: target,
          finder: finder
        });
      } else {
        auctionID = data.id;
        itemName = data.auction.itemName;
        if (bot.state !== 'moving') {
          logmc(`§3Adding ${itemName}§3 to the pipeline because state is ${bot.state}!`);
          stateManger.add(noColorCodes(itemName).replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, ""), 69, 'buying');
        }
      }
      idQueue.push(data.id);
      targetQueue.push(data.target);
      finderQueue.push(data.finder);
      const ending = new Date(normalizeDate(data.auction.start)).getTime() + 20000;
      webhookPricingMap.set(noColorCodes(itemName).replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, ""), {
        target: data.target,
        price: data.auction.startingBid,
        auctionId: auctionID,
        bed: bed,
        finder: data.finder,
      });
      if (currentTime < ending) {
        bed = '[BED]';
        webhookPricingMap.get(noColorCodes(itemName).replace(/!|-us|\.|\b(?:[1-9]|[1-5][0-9]|6[0-4])x\b/g, "")).bed = bed;
        setTimeout(async () => {
          for (let i = 0; i < 5; i++) {
            if (getWindowName(bot.currentWindow)?.includes('BIN Auction View')) {
              bot.clickWindow(31, 0, 0);
              await sleep(3);
            }
          }
        }, ending - currentTime - waittime);
        setTimeout(() => {
          if (getWindowName(bot.currentWindow)?.includes('BIN Auction View') && currentOpen === auctionID) {
            bot.closeWindow(bot.currentWindow);
            bot.state = null;
            logmc(`§6[§bTPM§6] §cBed timing failed and we had to abort the auction :(`);
          }
        }, 5000);
      }
    }
    debug(`Found flip ${itemName} uuid ${auctionID}`);
  });

  setInterval(() => {
    if (!bedSpam && !bedFailed) return;
    if (getWindowName(bot.currentWindow)?.includes('BIN Auction View')) {
      const item = bot.currentWindow?.slots[31]?.name;
      if (item?.includes('bed')) {
        bot.currentWindow.requiresConfirmation = false;
        bot.clickWindow(31, 0, 0);
      }
    }
  }, clickDelay);

  function sendScoreboard() {
    setTimeout(() => {
      if (!bot?.scoreboard?.sidebar?.items) return;
      if (bot.scoreboard.sidebar.items.map(item => item.displayName.getText(null).replace(item.name, '')).find(e => e.includes('Purse:') || e.includes('Piggy:'))) {
        send(
          JSON.stringify({
            type: 'uploadScoreboard',
            data: JSON.stringify(bot.scoreboard.sidebar.items.map(item => item.displayName.getText(null).replace(item.name, '')))
          })
        );
      }
    }, 5500);
  }

  ws.on('open', sendScoreboard);

  const settings = msg => {
    privacySettings = new RegExp(msg.chatRegex);
    ws.off('settings', settings);
  };

  ws.on('settings', settings);

  bot.on('chat', (username, message, type) => {
    if (!privacySettings) return;
    if (type === 'chat') {
      const msg = message.getText(null);
      if (privacySettings.test(msg)) {
        send(
          JSON.stringify({
            type: 'chatBatch',
            data: JSON.stringify([msg]),
          })
        );
      }
    }
  });

  const sendInventory = () => {
    send(
      JSON.stringify({
        type: 'uploadInventory',
        data: JSON.stringify(bot.inventory),
      })
    );
  };

  ws.on('getInventory', sendInventory);
  bot.on('windowOpen', sendInventory);
}

start();
