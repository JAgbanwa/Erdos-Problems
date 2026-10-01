// Local-only browser QA: no external page navigation or network dependencies.
const fs = require('fs');
const path = require('path');
const {pathToFileURL} = require('url');
const {chromium} = require(process.env.PLAYWRIGHT_MODULE);
const root = path.resolve(__dirname,'../../../..');
const out = process.argv[2];
if (!out) throw new Error('Provide an output directory outside the repository');
fs.mkdirSync(out,{recursive:true});
(async()=>{
  const browser=await chromium.launch({channel:'msedge',headless:true});
  const page=await browser.newPage();
  const errors=[];page.on('pageerror',e=>errors.push(e.message));
  const external=[];
  await page.route(/^https?:/,route=>{external.push(route.request().url());return route.abort();});
  const results=[];
  await page.setViewportSize({width:1200,height:900});
  await page.goto(pathToFileURL(path.join(root,'index.html')).href);
  await page.screenshot({path:path.join(out,'series-desktop.png'),fullPage:true});
  await page.goto(pathToFileURL(path.join(root,'preprints/PAPER_IV/PaperIV_explained_4_levels.html')).href);
  for(const width of [1200,390]){
    await page.setViewportSize({width,height:900});
    for(const lang of ['en','es']){
      await page.locator(`[data-lang="${lang}"]`).click();
      for(let level=0;level<=4;level++){
        await page.locator(`[data-level="${level}"]`).click();
        const data=await page.evaluate(()=>({lang:document.documentElement.lang,visible:[...document.querySelectorAll('.level')].filter(x=>!x.hidden).map(x=>x.id),overflow:document.documentElement.scrollWidth>innerWidth+1,brokenImages:[...document.images].filter(i=>!i.complete||!i.naturalWidth).map(i=>i.getAttribute('src'))}));
        if(data.lang!==lang||data.visible.join()!==`level-${level}`||data.overflow||data.brokenImages.length)throw new Error(JSON.stringify(data));
        results.push({width,lang,level,...data});
        await page.screenshot({path:path.join(out,`paperiv-${lang}-${level}-${width}.png`),fullPage:true});
      }
    }
  }
  if(errors.length||external.length)throw new Error(JSON.stringify({errors,external}));
  await browser.close();
  const result={status:'PASS',cases:results.length,external_requests:external,errors,results};
  fs.writeFileSync(path.join(root,'preprints/PAPER_IV/02_validation/03_EDITORIAL_CHECKS/v1.23/WEB_CHECKS.json'),JSON.stringify(result,null,2)+'\n');
  console.log(JSON.stringify({status:'PASS',cases:results.length,external_requests:external.length}));
})().catch(e=>{console.error(e);process.exit(1)});
