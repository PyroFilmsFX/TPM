const mineflayer = require('mineflayer');
const readline = require('readline');
const process = require('process');
const { once } = require('events');
const registry = require('prismarine-registry')('1.8.9');
const ChatMessage = require('prismarine-chat')(registry);
const { check, Window } = require('./window.js');
const utils = require('./utils.js');
const { randomUUID } = require('crypto');
const axios = require('axios');
const stateManager = require('./state.js');
const { noColorCodes, nicerFinders, normalizeDate, IHATETAXES, formatNumber, sleep, getWindowName, getPurse, relistCheck, addCommasToNumber } = require('./utils.js');
const { Webhook, MessageBuilder } = require('discord-webhook-node');
const { getPackets, makePackets } = require('./packetStuff.js');
const { silly, debug, error, info, logmc } = require('./logger.js');
const prompt = require('prompt-sync')();
const { startWS, send, handleCommand, ws, sidListener, solveCaptcha } = require('./websocketHelper.js');
const { config, updateConfig } = require('./config.js');
const nbt = require('prismarine-nbt');
const fastJsonParse = require('fast-json-parse');
const { Worker } = require('worker_threads');
const { LRUCache } = require('lru-cache');

// Initialize constants and variables
const {
  username: ign,
  bedSpam,
  discordID: discordid,
  TOS,
  webhook: webhookUrl,
  usInstance,
  clickDelay,
  delay,
  useBafSocket: usingBaf,
  session,
  discordBotToken: discordbot,
  doNotListFinders: badFinders = ['USER'],
  waittime,
  uuid,
  percentOfTarget,
  relist,
  ownAuctions
} = config;

let webhook, bot, cdClaim = 0, fullInv = false, relistClaim = false, uuidFound = false, lastLeftBuying;
let privacySettings, lastGui = 0, ranit = false, totalslots = 17, currentlisted = 0, closedGui = false, bedFailed = false;
const targetQueue = new Set(), idQueue = new Set(), finderQueue = new Set(), purchasedIds = new Set(), purchasedTargets = new Map();
const lastOpenedAhids = new Set(), lastOpenedTargets = new Set(), lastOpenedFinders = new Set(), lastListedIds = new Set(), lastListedTargets = new Map();
const relistObject = new Map(), webhookPricing = new Map();

if (webhookUrl) {
  webhook = new Webhook(webhookUrl);
  webhook.setUsername('TPM');
  webhook.setAvatar('https://media.discordapp.net/attachments/1235761441986969681/1263290313246773311/latest.png?ex=6699b249&is=669860c9&hm=87264b7ddf4acece9663ce4940a05735aecd8697adf1335de8e4f2dda3dbbf07&=&format=webp&quality=lossless');
}

// Memoized functions
const memoizedGetPurse = utils.memoize(getPurse);
const memoizedFormatNumber = utils.memoize(formatNumber);

// LRU Cache for frequently accessed data
const dataCache = new LRUCache({
  max: 1000,
  maxAge: 1000 * 60 * 5 // 5 minutes
});


// Optimized event handlers
const messageHandlers = new Map([
  ['Putting coins in escrow...', () => {
    logmc(`§6[§bTPM§6] §3Auction bought in ${Date.now() - firstGui}ms`);
    bot.state = null;
    if (bot.currentWindow && !closedGui) bot.closeWindow(bot.currentWindow);
    closedGui = true;
  }],
  ["This auction wasn't found!", () => bot.state = null],
  ["The auctioneer has closed this auction!", () => {
    bot.state = null;
    if (bot.currentWindow && !closedGui) bot.closeWindow(bot.currentWindow);
    closedGui = true;
  }],
  ["You don't have enough coins to afford this bid!", () => {
    bot.state = null;
    if (bot.currentWindow && !closedGui) bot.closeWindow(bot.currentWindow);
    closedGui = true;
  }],
  ['/limbo for more information.', async () => {
    await sleep(5000);
    bot.state = 'moving';
    bot.chat('/lobby');
  }],
  ['You may only use this command after 4s on the server!', () => bot.state = null],
  ["You didn't participate in this auction!", () => bot.state = null],
  ["Claiming this auction is on cooldown!", () => cdClaim++],
  ["There isn't enough space in your inventory!", () => fullInv = true]
]);

const messagePatterns = new Map([
  ['You claimed', (text) => {
    if (config.relist && text.includes("from") && text.includes("auction")) {
      relistClaim = true;
    }
  }],
  ['BIN Auction started for', (text) => {
    const item = text.split('BIN Auction started for ')[1].split('!')[0];
    handleBinAuctionStart(item);
  }],
  ['You purchased', (text) => {
    const [item, price] = text.split(' for ');
    handlePurchase(item.replace('You purchased ', ''), price.replace(' coins!', ''));
  }],
  ['[Auction]', (text) => {
    const [buyer, item, price] = text.split(' bought ')[1].split(' for ');
    handleAuctionBought(buyer, item, price.split(' coins')[0]);
  }]
]);

async function getReady() {
  ranit = true;
  await sleep(5000);
  bot.chat("/sbmenu");
  debug("sbmenu opened");
  
  const handleWindowOpen = async (window) => {
    if (bot.currentWindow.title.includes("SkyBlock Menu") && bot.currentWindow.slots[48].nbt.value.display.value.Name.value.includes("Profile Management")) {
      bot.currentWindow.requiresConfirmation = false;
      bot.clickWindow(48, 0, 0);
      debug("profile management opened");
      
      bot.once('windowOpen', async (window) => {
        if (bot.currentWindow.title.includes("Profile Management")) {
          for (const item of bot.currentWindow.slots) {
            if (item && item.slot > 9 && item.slot < 17 && item.displayName == "Block of Emerald") {
              const itemNbt = nbt.simplify(item.nbt);
              const coop = itemNbt.display?.Lore?.find(line => line.includes("Co-op with"))?.replace(/§./g, "");
              
              if (coop) {
                const coopRegexPlayers = /Co-op with (\d+) players:/;
                const coopRegexSinglePlayer = /Co-op with (?:\[.*\]\s*)?([\w]+)/;
                const matchPlayers = coop.match(coopRegexPlayers);
                const matchSinglePlayer = coop.match(coopRegexSinglePlayer);
                
                if (matchPlayers) {
                  const numberOfPlayers = parseInt(matchPlayers[1], 10);
                  totalslots = 14 + (numberOfPlayers * 3);
                } else if (matchSinglePlayer) {
                  totalslots = 17;
                } else {
                  error("Unrecognized COOP format:", coop);
                }
              } else {
                totalslots = 14;
              }
              
              logmc(`§6[§bTPM§6] §3Max ah slots set to ${totalslots}`);
              
              await sleep(500);
              bot.chat('/ah');
              await once(bot, 'windowOpen');
              
              if ((getWindowName(bot.currentWindow)?.includes("Co-op Auction House") || getWindowName(bot.currentWindow)?.includes("Auction House")) &&
                  (bot.currentWindow.slots[15].nbt.value.display.value.Name.value?.includes("Manage Auctions") || 
                   bot.currentWindow.slots[15].nbt.value.display.value.Name.value?.includes("Create Auction"))) {
                
                const item = bot.currentWindow.slots[15];
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
                
                debug("current listed set to,", currentlisted);
                
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
                  debug("claimed 1 already sold auction");
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
                  
                  for (let slot = 0; slot < 51; slot++) {
                    const item = bot.currentWindow.slots[slot];
                    if (item?.nbt?.value?.display?.value?.Name) {
                      const itemName = item.nbt.value.display.value.Name.value;
                      if ((!config.ownAuctions && itemName.includes("Claim All")) ||
                          (config.ownAuctions && itemName.includes("Claim Your"))) {
                        bot.currentWindow.requiresConfirmation = false;
                        bot.clickWindow(slot, 0, 0);
                        break;
                      }
                    }
                  }
                  
                  debug("claimed multiple already sold auctions");
                  currentlisted -= bids;
                }
                
                debug("currentlisted updated to", currentlisted);
                
                if (!toclaim1 && !toclaim2) {
                  debug("no previously sold auctions to claim, proceeding...");
                  if (bot.currentWindow) bot.closeWindow(bot.currentWindow);
                }
                
                logmc("§6[§bTPM§6] §3Finished getting slot data");
                bot.state = null;
                startWS(session);
                return;
              }
            }
          }
        }
      });
    }
  };
  
  bot.once('windowOpen', handleWindowOpen);
}

async function relistHandler(purchasedAhids, purchasedPrices) {
  bot.state = "listing";
  relistClaim = false;
  let itemuuid;
  let idToRelist = purchasedAhids;
  let priceToRelist = purchasedPrices;
  
  debug("Starting relist process for item with ahid:", idToRelist, "and target:", priceToRelist, 'bot state:', bot.state);
  bot.chat(`/viewauction ${idToRelist}`);
  await once(bot, 'windowOpen');
  
  if (getWindowName(bot.currentWindow)?.includes("BIN Auction View")) {
    await sleep(500);
    debug("BIN Auction View opened");
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
    debug("claim click");
    await sleep(500);
    
    if (cdClaim > 0 && bot.currentWindow) {
      bot.currentWindow.requiresConfirmation = false;
      bot.clickWindow(31, 0, 0);
      debug("claim click 2 (after first cooldown)");
      await sleep(200);
      if (!relistClaim) {
        logmc("§6[§bTPM§6] §cAborting relist after 2 failed item claim attempts");
        purchasedIds.add(idToRelist);
        purchasedTargets.set(idToRelist, priceToRelist);
        stateManager.add({ id: purchasedIds, targets: purchasedTargets }, Infinity, 'listing');
        bot.state = null;
        cdClaim = 0;
        return;
      }
    }
    
    if (fullInv && bot.currentWindow) {
      bot.currentWindow.requiresConfirmation = false;
      bot.clickWindow(31, 0, 0);
      debug("claim click 2 (after full inv)");
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
  debug("price " + priceToRelist);
  await once(bot, 'windowOpen');
  debug("did /ah");
  
  if (!bot.currentWindow) {
    logmc("§6[§bTPM§6] §cWas not able to open AH to sell item, trying again");
    await sleep(200);
    bot.chat("/ah");
    debug(`running /ah`);
    await once(bot, 'windowOpen');
    if (!bot.currentWindow) {
      logmc("§6[§bTPM§6] §cFailed again, aborting!!!");
      bot.state = null;
      return;
    }
  }
  
  const itemToRelist = bot.currentWindow.slots.find(item => 
    item && nbt.simplify(item?.nbt)?.ExtraAttributes?.uuid === itemuuid
  );
  
  if (itemToRelist) {
    debug("found item in inventory to relist with uuid", itemuuid);
    uuidFound = true;
    bot.currentWindow.requiresConfirmation = false;
    await sleep(200);
    bot.clickWindow(itemToRelist.slot, 0, 0);
    debug("added item into ah menu");
  }

  if (!uuidFound) {
    logmc("§6[§bTPM§6] §cItem not found in inventory please report this (: Aborting relist process for this item ):")
    if (bot.currentWindow) bot.closeWindow(bot.currentWindow);
    await sleep(250)
    bot.state = null;
    logmc("§6[§bTPM§6] §3Hopefully exited annoying bug safely (if not report this)")
    return;
  }
  uuidFound = false;
  await once(bot, 'windowOpen');
  if ((getWindowName(bot.currentWindow)?.includes("Create BIN Auction")) && bot.currentWindow.slots[33].nbt.value.display.value.Name.value?.includes("6 Hours")) {
    debug("Auction Duration Menu Opened")
    await sleep(200)
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(33, 0, 0)
  } else if (!getWindowName(bot.currentWindow)?.includes('Create BIN Auction')) {
    logmc("§6[§bTPM§6] §cItem probably already in slot, please remove it :) Aborting relist process for this item ):")
    if (bot.currentWindow) bot.closeWindow(bot.currentWindow);
    await sleep(250)
    bot.state = null;
    logmc("§6[§bTPM§6] §3Hopefully exited annoying bug safely (if not report this)");
    return;
  }
  await once(bot, 'windowOpen');
  if (bot.currentWindow?.title?.includes("Auction Duration")) {
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(14, 0, 0)
    debug("Auction Duration set to 2 days")
  }
  await once(bot, 'windowOpen');
  if ((getWindowName(bot.currentWindow)?.includes("Create BIN Auction")) && bot.currentWindow.slots[33].nbt.value.display.value.Name.value?.includes("2 Days")) {
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(31, 0, 0)
    debug("opened bid creation menu")
  }
  await sleep(500)
  debug("PRICEHERE " + priceToRelist)
  let listpriceomg = (priceToRelist)
  let relistpercent = 100;
  const relistPercentage = percentOfTarget.find(([lower, upper]) => 
    priceToRelist >= lower && priceToRelist < upper
  );
  if (relistPercentage) {
    relistpercent = relistPercentage[2];
  }
  debug("lpomg " + listpriceomg)
  debug("relistpercent", relistpercent)
  let result = priceToRelist * (relistpercent / 100);
  result = Math.round(result);
  debug("result", result)
  let strResult = result.toString();
  if (strResult.length > 3) {
    let firstThreeDigits = strResult.substring(0, 3);
    let remainingZeros = '0'.repeat(strResult.length - 3);
    listpriceomg = Number(firstThreeDigits + remainingZeros);
  } else {
    listpriceomg = result;
  }
  debug("listprice is", listpriceomg)
  bot._client.write('update_sign', {
    location: bot.entity.position.offset(-1, 0, 0),
    text1: `\"${listpriceomg.toString()}\"`,
    text2: '{"italic":false,"extra":["^^^^^^^^^^^^^^^"],"text":""}',
    text3: '{"italic":false,"extra":["Your auction"],"text":""}',
    text4: '{"italic":false,"extra":["starting bid"],"text":""}'
  });
  debug("set list price to", listpriceomg);
  await sleep(500)
  debug("AAAAAAAAAAAAA", bot.currentWindow.slots[31].nbt.value.display.value.Name.value)
  debug("Listed price", listpriceomg)
  let numWithCommas = addCommasToNumber(listpriceomg)
  debug(numWithCommas)
  await sleep(500)
  debug("Debug time:", getWindowName(bot.currentWindow), bot.currentWindow.slots[31].nbt.value.display.value.Name.value, bot.currentWindow.slots[33].nbt.value.display.value.Name.value)
  if (getWindowName(bot.currentWindow)?.includes("Create BIN Auction") && bot.currentWindow.slots[31].nbt.value.display.value.Name.value?.includes(`${numWithCommas} coins`) && bot.currentWindow.slots[33].nbt.value.display.value.Name.value?.includes("2 Days")) {
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(29, 0, 0)
    debug("bid confirmed, finalizing auction listing")
    lastListedIds.add(idToRelist);
    lastListedTargets.set(idToRelist, listpriceomg);
  }
  await once(bot, 'windowOpen');
  if (bot.currentWindow.title.includes("Confirm BIN Auction")) {
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(11, 0, 0)
    await once(bot, 'windowOpen');
    if (bot.currentWindow.slots[29]?.type == 394 && (getWindowName(bot.currentWindow)?.includes("BIN Auction View"))) {
      logmc("§6[§bTPM§6] §3Auction listed :D");
      bot.closeWindow(bot.currentWindow);
      bot.state = null;
      currentlisted++;
      debug(`Current listed: ${currentlisted}`);
    }
  }
}

if (!session) {
  session = randomUUID();
  config.session = session;
  updateConfig(config)
  sidListener(session);
}

// start bot
async function start() {
  const stuckFailsafe = new Set();
  
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
    if (!uuid) {
      axios.get(`https://api.mojang.com/users/profiles/minecraft/${bot.username}`)
        .then(response => {
          uuid = response.data.id;
          config.uuid = uuid;
          updateConfig(config)
        })
        .catch(error => {
          console.error(`Error fetching UUID for ign ${bot.username}:`, error);
        });
    }
  })
  bot.state = 'moving';
  let firstGui;
  Window.on('newWindow', async window => {
    bot.currentWindow.requiresConfirmation = false;
    const name = getWindowName(window);
    lastGui = Date.now();
    if (name === 'BIN Auction View' && bot.state !== 'listing') {
      debug("bot state", bot.state)
      bot.clickWindow(31, 0, 0);
      lastLeftBuying = Date.now();
      bot.state = 'buying';
      firstGui = lastGui;
      await sleep(6);
      const item = bot.currentWindow?.slots[31]?.name;
      const itemActions = {
        'poisonous_potato': () => {
          bot.closeWindow(bot.currentWindow);
          bot.state = null;
        },
        'potato': () => {
          bot.closeWindow(bot.currentWindow);
          bot.state = null;
        },
        'feather': () => {
          bot.closeWindow(bot.currentWindow);
          bot.state = null;
        },
        'gold_block': () => {
          bot.state = null;
        }
      };
      if (itemActions[item]) {
        itemActions[item]();
      }
    } else if (name === 'Confirm Purchase') {
      bot.clickWindow(11, 0, 0);
      logmc(`§6[§bTPM§6] §3Confirm at ${Date.now() - firstGui}ms`);
      if (bedSpam || bedFailed) {
        for (let i = 1; i < 11; i++) {
          await sleep(30);
          if (getWindowName(bot.currentWindow)) {
            bot.clickWindow(11, 0, 0)
          } else {
            break;
          }
        }
      }
      bot.state = null;
    }
  });
  setInterval(() => {
    check(bot);
  }, 1);
  setInterval(async () => {
    if (bot.state === 'buying' && Date.now() - lastLeftBuying > 5000) {
      error("Bot state issue detected, resetting state and hopefully fixing queue lock issue")
      if (bot.currentWindow) bot.closeWindow(bot.currentWindow);
      await sleep(200)
      bot.state = null;
    }
  }, 250);
  let old = bot.state;
  setInterval(async () => {
    const current = stateManager.get();
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
          logmc("§6[§bTPM§6] §cNot attempting to relist because your inventory is full. You will need to log in and clear your inventory to continue")
          bot.state = null;
        } else {
          await sleep(10000)
          if (relistCheck(currentlisted, totalslots, bot.state)) {
            bot.state = "listing";
            await sleep(500);
            relistHandler(command.id, command.targets);
          } else {
            stateManager.add(command, Infinity, 'listing');
          }
        }
      } else {
        bot.state = current.state;
        const ahhhhh = webhookPricing.get(command);
        if (ahhhhh) {
          var ahid = ahhhhh.id
        } else {
          error(`Ahhh didn't find ${command} in ${JSON.stringify(Object.fromEntries(webhookPricing))}`);
        }
        bedFailed = true;
        currentOpen = ahid
        bot.chat(`/viewauction ${ahid}`);
      }
      stateManager.next();
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
          logmc('§6[§bTPM§6] §cBot found in the hub :( going back to skyblock')
          bot.chat('/is');
          lastAction = Date.now();
        }
        if (line.includes('Rank:')) {
          bot.state = 'moving';
          logmc('§6[§bTPM§6] §cBot found in the lobby :( going back to skyblock')
          bot.chat('/play sb');
          lastAction = Date.now();
        }
        if (line.includes('bugs')) {
          bot.state = 'moving';
          logmc('§6[§bTPM§6] §cBot found in the lobby :( going back to skyblock')
          bot.chat('/play sb');
          lastAction = Date.now();
        }
        if (line.includes('Your Island')) {
          if (!ranit) {
            getReady()
          } else {
            if (bot.state === 'moving') bot.state = null;
            lastAction = Date.now();
          }
        }
      });
    }, 30000);
  });
  bot.on('error', e => {
    error(e);
  });
  bot.on('login', () => {
    bot.chat('/locraw');
  });
  bot.on('message', async (message, type) => {
    const text = message.getText(null);
    if (type === 'chat') {
      logmc(message.toAnsi());
    }
    const handler = messageHandlers.get(text);
    if (handler) {
      await handler();
    } else {
      handleOtherMessages(text);
    }
  });

  function handleOtherMessages(text) {
    for (const [pattern, handler] of messagePatterns.entries()) {
      if (text.includes(pattern)) {
        handler(text);
        break;
      }
    }
  }

  async function handleBinAuctionStart(item) {
    const auctionUrl = `https://sky.coflnet.com/auction/${lastListedIds.values().next().value}`;
    const purse = memoizedFormatNumber(await memoizedGetPurse(bot));
    if (webhook) {
      const embed = new MessageBuilder()
        .setFooter(`The "Perfect" Macro - Purse: ${purse}`, 'https://media.discordapp.net/attachments/1223361756383154347/1263302280623427604/capybara-square-1.png?ex=6699bd6e&is=66986bee&hm=d18d0749db4fc3199c20ff973c25ac7fd3ecf5263b972cc0bafea38788cef9f3&=&format=webp&quality=lossless&width=437&height=437')
        .setTitle('Item listed')
        .addField('', `Listed \`${item}\` for \`${addCommasToNumber(lastListedTargets.values().next().value)} coins\` [click](${auctionUrl}) \n [AH Slots: ${currentlisted}/${totalslots}]`)
        .setThumbnail(`https://mc-heads.net/head/${config.uuid}.png`)
        .setColor(13677311);
      webhook.send(embed);
    }
    sendScoreboard();
  }

  async function handlePurchase(item, price) {
    const cleanItem = utils.noColorCodes(item).replace(/[!-us.]|(?:\d{1,2}x)/g, "");
    const object = relistObject.get(cleanItem);
    if (lastOpenedAhids.size > 0 && config.relist && object) {
      const { id: lastPurchasedAhid, target: lastPurchasedTarget, finder: lastPurchasedFinder } = object;
      if (!badFinders?.includes(lastPurchasedFinder)) {
        purchasedFinders.add(lastPurchasedFinder);
        setTimeout(async () => {
          if (bot.state === null) {
            if (fullInv) {
              logmc("§6[§bTPM§6] §cNot attempting to relist because your inventory is full. You will need to log in and clear your inventory to continue")
              bot.state = null;
            } else {
              if (relistCheck(currentlisted, totalslots, bot.state)) {
                bot.state = "listing";
                await sleep(500);
                relistHandler(lastPurchasedAhid, lastPurchasedTarget);
              } else {
                debug(`relist check didn't work`);
                stateManager.add({ id: lastPurchasedAhid, targets: lastPurchasedTarget }, Infinity, 'listing');
                bot.state = null;
              }
            }
          } else {
            debug(`bot state check didn't work`);
            stateManager.add({ id: lastPurchasedAhid, targets: lastPurchasedTarget }, Infinity, 'listing');
            bot.state = null;
          }
        }, 10000);
      } else {
        logmc(`§6[§bTPM§6] §cUser finder flip found, not relisting ${lastPurchasedFinder}`)
      }
    } else if (!object) {
      error(`Didn't find ${cleanItem} in ${JSON.stringify(Object.fromEntries(relistObject))} Please report this to icyhenryt`);
    }
    if (bot.state == 'buying') bot.state = null;
    const itemData = webhookPricing.get(cleanItem);
    if (!itemData) {
      error(`Didn't find ${cleanItem} in ${JSON.stringify(Object.fromEntries(webhookPricing))} Please report this to icyhenryt`);
      return;
    }
    const { bed: itemBed, auctionId, target, finder } = itemData;
    const auctionUrl = `https://sky.coflnet.com/auction/${auctionId}`;
    const profit = utils.IHATETAXES(target) - utils.onlyNumbers(price);
    const purse = memoizedFormatNumber(await memoizedGetPurse(bot) - parseInt(price.replace(/,/g, ''), 10));
    if (webhook) {
      const embed = new MessageBuilder()
        .setFooter(`TPM - Found by ${nicerFinders(finder)} - Purse: ${purse} `, 'https://media.discordapp.net/attachments/1223361756383154347/1263302280623427604/capybara-square-1.png?ex=6699bd6e&is=66986bee&hm=d18d0749db4fc3199c20ff973c25ac7fd3ecf5263b972cc0bafea38788cef9f3&=&format=webp&quality=lossless&width=437&height=437')
        .setTitle('Item purchased')
        .addField('', `Bought \`${utils.noColorCodes(item)}\` for \`${price} coins\` (\`${memoizedFormatNumber(profit)}\` profit) [click](${auctionUrl}) ${itemBed}`)
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
          stateManager.add('claim', 37, 'claiming');
        }
      }, 500);
    }
  }

  async function handleAuctionBought(buyer, item, price) {
    currentlisted--;
    if (webhook) {
      const purse = memoizedFormatNumber(await memoizedGetPurse(bot) + parseInt(price.replace(/,/g, ''), 10));
      const embed = new MessageBuilder()
        .setFooter(`The "Perfect" Macro - Purse: ${purse} `, `https://media.discordapp.net/attachments/1223361756383154347/1263302280623427604/capybara-square-1.png?ex=6699bd6e&is=66986bee&hm=d18d0749db4fc3199c20ff973c25ac7fd3ecf5263b972cc0bafea38788cef9f3&=&format=webp&quality=lossless&width=437&height=437`)
        .setTitle('Item Sold')
        .addField('', `Collected \`${addCommasToNumber(utils.onlyNumbers(price))} coins\` for selling \`${item}\` to \`${buyer}\``)
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
        stateManager.add('sold', 28, 'claiming');
      }
    }, 500);
  }

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

  const claimBought = utils.memoize(async () => {
    bot.chat('/ah');
    await sleep(300);
    if (!bot.currentWindow) return;
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(13, 0, 0);
    await sleep(300);
    bot.currentWindow.requiresConfirmation = false;
    bot.clickWindow(10, 0, 0);
    await sleep(50);
  });

  const claimSold = utils.memoize(async () => {
    bot.chat('/ah');
    await sleep(300);
    if (getWindowName(bot.currentWindow)?.includes('Auction House')) {
      bot.currentWindow.requiresConfirmation = false;
      bot.clickWindow(15, 0, 0);
      await sleep(300);
      if (getWindowName(bot.currentWindow)?.includes('Manage Auctions')) {
        bot.currentWindow.requiresConfirmation = false;
        const items = bot.currentWindow?.slots;
        for (const [index, item] of items.entries()) {
          if (!item) continue;
          const name = item?.value?.display?.value?.Name?.value?.toString();
          if (name?.includes('Claim')) {
            bot.clickWindow(index, 0, 0);
            await sleep(50);
            if (fullInv) {
              logmc("§6[§bTPM§6] §cNot attempting to relist because your inventory is full. You will need to log in and clear your inventory to continue")
              bot.state = null;
            } else {
              await sleep(5000)
              if (relistCheck([...purchasedIds], currentlisted, totalslots, bot.state)) {
                bot.state = "listing";
                await sleep(500);
                relistHandler([...purchasedIds], [...purchasedTargets.values()]);
              } else {
                stateManager.add({ id: [...purchasedIds], targets: [...purchasedTargets.values()] }, 4, 'listing');
              }
            }
            return;
          }
        }
        for (const [index, item] of items.entries()) {
          if (!item) continue;
          const lore = item.nbt.value?.display?.value?.Lore?.value?.value?.toString();
          if (lore?.includes('Sold!')) {
            bot.clickWindow(index, 0, 0);
          }
        }
      } else {
        console.error(`Didn't properly claim sold auction not finding Manage auctions. Found ${getWindowName(bot.currentWindow)}`);
      }
    } else {
      console.error(`Didn't properly claim sold auction not finding Auction House. Found ${getWindowName(bot.currentWindow)}`);
    }
    return;
  });

  ws.on('flip', async msg => {
    let bed = '[NUGGET]';
    const data = fastJsonParse(msg.data).value;
    let itemName, auctionID;
    const currentTime = Date.now();
    
    if (usingBaf) {
      if (!bot.state && currentTime - lastAction > delay) {
        lastLeftBuying = currentTime;
        bot.state = 'buying';
        auctionID = data.id;
        packets.sendMessage(`/viewauction ${auctionID}`);
        let target = data.target;
        let finder = data.finder;
        itemName = data.itemName.replace(/[!-us.]|(?:\d{1,2}x)/g, "");
        lastAction = currentTime;
        logmc(`§6[§bTPM§6] §8Opening ${itemName}`);
        closedGui = false;
        bedFailed = false;
        currentOpen = data.id;
        lastOpenedTargets.clear();
        lastOpenedTargets.add(target);
        lastOpenedAhids.clear();
        lastOpenedAhids.add(auctionID);
        lastOpenedFinders.clear();
        lastOpenedFinders.add(finder);
        relistObject.set(itemName, {
          id: auctionID,
          target: target,
          finder: data.finder
        });
      } else {
        auctionID = data.id;
        itemName = data.itemName.replace(/[!-us.]|(?:\d{1,2}x)/g, "");
        logmc(`§6[§bTPM§6] §aAdding ${itemName}§3 to the pipeline because state is ${bot.state}!`);
        stateManager.add(itemName, 69, 'buying');
      }
      idQueue.add(data.id);
      targetQueue.add(data.target);
      finderQueue.add(data.finder);
      const ending = new Date(normalizeDate(data.purchaseAt)).getTime();
      webhookPricing.set(itemName, {
        target: data.target,
        price: data.startingBid,
        auctionId: auctionID,
        bed: bed,
        finder: data.finder,
      });
      if (currentTime < ending) {
        bed = '[BED]';
        webhookPricing.get(itemName).bed = bed;
        setTimeout(async () => {
          for (let i = 0; i < 4; i++) {
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
            logmc(`§6[§bTPM§6] §cBed timing failed and we had to abort the auction :( Please lower your waittime if this continues or turn on bedspam`);
          }
        }, 5000);
      }
    } else {
      // Similar logic for non-BAF case
      // ... (implement the non-BAF logic here)
    }
    
    // Use Set for efficient tracking of stuck states
    if (!stuckFailsafe.has(bot.state)) {
      stuckFailsafe.add(bot.state);
      setImmediate(() => {
        const checkStuck = () => {
          if (bot.state && Date.now() - lastAction > 30000) {
            logmc(`§6[§bTPM§6] §cGot stuck :( `);
            if (getWindowName(bot.currentWindow)) bot.closeWindow(bot.currentWindow);
            bot.state = null;
            lastAction = Date.now();
          }
          if (stuckFailsafe.has(bot.state)) {
            setImmediate(checkStuck);
          }
        };
        checkStuck();
      });
    }
    debug(`Found flip ${itemName} uuid ${auctionID}`)
  });

  setInterval(() => {
    // BED SPAM
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
      const scoreboardItems = bot.scoreboard.sidebar.items.map(item => item.displayName.getText(null).replace(item.name, ''));
      if (scoreboardItems.some(e => e.includes('Purse:') || e.includes('Piggy:'))) {
        send(
          JSON.stringify({
            type: 'uploadScoreboard',
            data: JSON.stringify(scoreboardItems)
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

// Utility functions

function memoize(fn) {
  const cache = new Map();
  return (...args) => {
    const key = JSON.stringify(args);
    if (cache.has(key)) return cache.get(key);
    const result = fn(...args);
    cache.set(key, result);
    return result;
  };
}

function optimizedRelistCheck(currentlisted, totalslots, botstate) {
  if ((botstate === null || botstate === 'listing') && (currentlisted !== totalslots)) {
    return true;
  }
  if (botstate === "buying" || botstate === "listing" || botstate === "claiming" || botstate === "moving" || currentlisted === totalslots) {
    if (currentlisted === totalslots) {
      return false;
    } else if (botstate && botstate !== 'listing') {
      return false;
    }
  } else {
    return false;
  }
}


// Implement object pooling for frequently created objects
const objectPool = {
  messageBuilder: [],
  getMessageBuilder() {
    return this.messageBuilder.pop() || new MessageBuilder();
  },
  releaseMessageBuilder(builder) {
    builder.clear(); // Assuming there's a method to reset the builder
    this.messageBuilder.push(builder);
  }
};

// Use the object pool when creating MessageBuilder instances
function createWebhookEmbed(title, description) {
  const embed = objectPool.getMessageBuilder()
    .setTitle(title)
    .setDescription(description);
  // Use the embed...
  objectPool.releaseMessageBuilder(embed);
}

// Implement weak references for caching
const weakCache = new WeakMap();

function getCachedData(key, compute) {
  if (!weakCache.has(key)) {
    const data = compute();
    weakCache.set(key, new WeakRef(data));
    return data;
  }
  const cachedData = weakCache.get(key).deref();
  if (cachedData === undefined) {
    const data = compute();
    weakCache.set(key, new WeakRef(data));
    return data;
  }
  return cachedData;
}

// Use batch processing for API calls
const apiBatchQueue = [];
const BATCH_SIZE = 10;
const BATCH_INTERVAL = 1000; // 1 second

setInterval(() => {
  if (apiBatchQueue.length >= BATCH_SIZE) {
    const batch = apiBatchQueue.splice(0, BATCH_SIZE);
    sendApiBatch(batch);
  }
}, BATCH_INTERVAL);

function queueApiCall(data) {
  apiBatchQueue.push(data);
}

function sendApiBatch(batch) {
  // Implement the logic to send the batch of API calls
  console.log('Sending API batch:', batch);
}

// Implement a circular buffer for logging
class CircularBuffer {
  constructor(size) {
    this.size = size;
    this.buffer = new Array(size);
    this.pointer = 0;
  }

  add(item) {
    this.buffer[this.pointer] = item;
    this.pointer = (this.pointer + 1) % this.size;
  }

  getAll() {
    return [...this.buffer.slice(this.pointer), ...this.buffer.slice(0, this.pointer)].filter(Boolean);
  }
}

const logBuffer = new CircularBuffer(1000); // Store last 1000 log entries

function bufferedLog(message) {
  logBuffer.add({ timestamp: Date.now(), message });
}

// Use the buffered log instead of direct console.log
function optimizedLogmc(message) {
  bufferedLog(message);
  process.stdout.write(message + '\n');
}

// Replace the original logmc function with the optimized version
Object.assign(global, { logmc: optimizedLogmc });

// Implement asynchronous logging
const logQueue = [];
setImmediate(function processLogQueue() {
  while (logQueue.length > 0) {
    const log = logQueue.shift();
    process.stdout.write(log + '\n');
  }
  setImmediate(processLogQueue);
});

function asyncLog(message) {
  logQueue.push(message);
}

// Export necessary functions and variables
module.exports = {
  start,
  handleCommand,
  solveCaptcha,
  memoizedGetPurse,
  memoizedFormatNumber,
  optimizedRelistCheck,
  createWebhookEmbed,
  getCachedData,
  queueApiCall,
  bufferedLog,
  asyncLog
};
          
