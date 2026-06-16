---
title: Phase 1 数学内容外部链接校验报告
level: meta
processed_at: '2026-06-16T12:46:24.166488'
review_status: draft
---

# Phase 1 数学内容外部链接校验报告

**校验时间**: 2026年06月16日 12:46
**校验范围**: docs/、concept/、数学家理念体系/、FormalMath-v2/、FormalMathLean4/、project/（排除 node_modules 等）
**检查链接总数**: 15899
**确认失效链接数**: 463 | **不确定/瞬态链接数**: 1825
**涉及唯一 URL 数**: 2426

## 一、按文档分类统计

| 分类 | 检查链接数 | 确认失效 | 不确定/瞬态 |
|------|-----------|---------|------------|
| 数学家理念体系 | 7197 | 55 | 1502 |
| docs | 6939 | 162 | 72 |
| project | 1001 | 230 | 221 |
| concept | 762 | 16 | 30 |

## 二、确认失效链接按域名汇总（Top 30）

| 域名 | 失效数 |
|------|-------|
| ncatlab.org | 71 |
| mathshistory.st-andrews.ac.uk | 35 |
| github.com | 31 |
| math.mit.edu | 18 |
| example.com | 15 |
| us.metamath.org | 13 |
| dev.w3.org | 13 |
| jsperf.com | 10 |
| www.math.princeton.edu | 9 |
| localhost:8001 | 8 |
| peterolson.github.io | 7 |
| leanprover-community.github.io | 6 |
| www.uni-goettingen.de | 6 |
| ocw.mit.edu | 6 |
| www.ens.fr | 6 |
| eslint.org | 6 |
| ecma-international.org | 6 |
| mysite.com | 6 |
| stacks.math.columbia.edu | 5 |
| heycam.github.io | 5 |
| 2ality.com | 5 |
| google.com | 5 |
| mathworld.wolfram.com | 4 |
| www.foo.com | 4 |
| json-schema.org | 4 |
| lodash.com | 4 |
| foo.com | 4 |
| nodejs.org | 4 |
| arxiv.org | 3 |
| leanprover.github.io | 3 |

## 三、确认失效链接清单（前 500 条）

| 文档路径 | 原链接 | 状态码 | 最终 URL |
|----------|--------|--------|----------|
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://' | [Errno 11001] getaddrinfo failed | http://' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://10.*.*.* | [Errno 11001] getaddrinfo failed | http://10.*.*.* |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://10.0.0.1:1234' | nonnumeric port: '1234'' | http://10.0.0.1:1234' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://10.255.255.1' | [Errno 11001] getaddrinfo failed | http://10.255.255.1' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://127.0.0.1:1336/amd-test | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://127.0.0.1:1336/amd-test |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://127.0.0.1:1336/browser-test | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://127.0.0.1:1336/browser-test |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://127.0.0.1:1336/browserify-test | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://127.0.0.1:1336/browserify-test |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://127.0.0.1:1337/ | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://127.0.0.1:1337/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://127.0.0.1:9001 | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://127.0.0.1:9001 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://168.63.76.32:3128' | 400 | http://168.63.76.32:3128' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://2ality.com/2017/05/regexp-lookbehind-assertions.html | 404 | https://2ality.com/2017/05/regexp-lookbehind-assertions.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://2ality.com/2017/05/regexp-named-capture-groups.html | 404 | https://2ality.com/2017/05/regexp-named-capture-groups.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://2ality.com/2017/07/regexp-unicode-property-escapes.html | 404 | https://2ality.com/2017/07/regexp-unicode-property-escapes.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://abc.com/~smith/home.html | 404 | https://abc.com/~smith/home.html |
| `docs/管理员手册/02-部署指南.md` | http://adaptive/ | [Errno 11001] getaddrinfo failed | http://adaptive/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://adaptive/ | [Errno 11001] getaddrinfo failed | http://adaptive/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://api:8000/metrics | [Errno 11001] getaddrinfo failed | http://api:8000/metrics |
| `docs/管理员手册/02-部署指南.md` | http://assessment/ | [Errno 11001] getaddrinfo failed | http://assessment/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://assessment/ | [Errno 11001] getaddrinfo failed | http://assessment/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://backend* | [Errno 11001] getaddrinfo failed | http://backend* |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://bl.ocks.org/mbostock/raw/4343214/thumbnail.png | 400 | https://gist.githubusercontent.com/mbostock/raw/4343214/thumbnail.png |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://bl.ocks.org/mbostock/raw/9078690/thumbnail.png | 400 | https://gist.githubusercontent.com/mbostock/raw/9078690/thumbnail.png |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://browsenpm.org/package/requires-port | 404 | https://browsenpm.org/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://browserify.org/)/ | 404 | https://browserify.org/%29/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://caniuse.com/#search=blob | 400 | http://caniuse.com/#search%3Dblob |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://caniuse.com/#search=promise | 400 | http://caniuse.com/#search%3Dpromise |
| `docs/管理员手册/02-部署指南.md` | http://cognitive_diagnosis/ | [Errno 11001] getaddrinfo failed | http://cognitive_diagnosis/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://cognitive_diagnosis/ | [Errno 11001] getaddrinfo failed | http://cognitive_diagnosis/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://corporate-spec-membership.graphql.org/ | 404 | http://corporate-spec-membership.graphql.org/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://cssinjs.org/)** | 404 | https://cssinjs.org/%29%2A%2A |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://data-arts.appspot.com/globe | 404 | http://data-arts.appspot.com/globe |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#adjacent-sibling-combinators | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#attribute-selectors | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#child-combinators | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#descendant-combinators | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#general-sibling-combinators | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#matches | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#negation-pseudo | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#subject | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#the-first-child-pseudo | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#the-last-child-pseudo | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#the-nth-child-pseudo | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#the-nth-last-child-pseudo | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dev.w3.org/csswg/selectors4/#universal-selector | 404 | https://drafts.csswg.org/selectors4/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://devtoolscommunity.herokuapp.com | 404 | http://devtoolscommunity.herokuapp.com |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://devtoolscommunity.herokuapp.com/badge.svg | 404 | http://devtoolscommunity.herokuapp.com/badge.svg |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dirk.jivas.de/papers/buchheim02improving.pdf | 404 | http://dirk.jivas.de/papers/buchheim02improving.pdf |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://donavon.com | 404 | https://donavon.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dperini.github.io/nwsapi/ | 404 | http://dperini.github.io/nwsapi/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ecma-international.org/ecma-262/6.0/#sec-future-reserved-words | 400 | http://ecma-international.org/ecma-262/6.0/#sec-future-reserved-words |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ecma-international.org/ecma-262/6.0/#sec-identifiers | 400 | http://ecma-international.org/ecma-262/6.0/#sec-identifiers |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ecma-international.org/ecma-262/6.0/#sec-identifiers-static-semantics-early-errors | 400 | http://ecma-international.org/ecma-262/6.0/#sec-identifiers-static-semantics-early-errors |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ecma-international.org/ecma-262/6.0/#sec-keywords | 400 | http://ecma-international.org/ecma-262/6.0/#sec-keywords |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ecma-international.org/ecma-262/6.0/#sec-names-and-keywords | 400 | http://ecma-international.org/ecma-262/6.0/#sec-names-and-keywords |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ecma-international.org/ecma-262/6.0/#sec-reserved-words | 400 | http://ecma-international.org/ecma-262/6.0/#sec-reserved-words |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://es5.github.io/#x7.6.1 | 400 | http://es5.github.io/#x7.6.1 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://es5.github.io/#x7.6.1.1 | 400 | http://es5.github.io/#x7.6.1.1 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://es5.github.io/#x7.6.1.2 | 400 | http://es5.github.io/#x7.6.1.2 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://eslint.org/docs/developer-guide/working-with-plugins#environments-in-plugins | 404 | https://eslint.org/docs/latest/extend/working-with-plugins%23environments-in-plugins |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://eslint.org/docs/developer-guide/working-with-plugins#environments-in-plugins).** | 404 | https://eslint.org/docs/latest/extend/working-with-plugins%23environments-in-plugins%29.%2A%2A |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://eslint.org/doctrine/demo/ | 404 | https://eslint.org/doctrine/demo/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/' | 404 | http://example.com/%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/app/js/ | 404 | http://example.com/app/js/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/fav.ico | 404 | http://example.com/fav.ico |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/fav.ico' | 404 | http://example.com/fav.ico%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/index.html' | 404 | http://example.com/index.html%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/otherpath | 404 | http://example.com/otherpath |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/schemas/defs.json | 404 | http://example.com/schemas/defs.json |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/schemas/schema.json | 404 | http://example.com/schemas/schema.json |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/schemas/schema.json' | 404 | http://example.com/schemas/schema.json%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/something' | 404 | http://example.com/something%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/src | 404 | http://example.com/src |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/whatever/?qs=32 | 404 | http://example.com/whatever/?qs=32 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/www/js/' | 404 | http://example.com/www/js/%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/www/js/one.js' | 404 | http://example.com/www/js/one.js%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com/www/js/two.js' | 404 | http://example.com/www/js/two.js%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.org/' | 404 | http://example.org/%27 |
| `project/arXiv追踪自动化方案.md` | http://export.arxiv.org/api/query | 400 | https://export.arxiv.org/api/query |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://facebook.github.io/react/docs/jsx-in-depth.html | 404 | http://facebook.github.io/react/docs/jsx-in-depth.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://foo.com/src | 404 | http://www.foo.com/src |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://foo.com/src',url='foo.min.js.map' | 404 | http://www.foo.com/src%27%2Curl%3D%27foo.min.js.map%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://foo.com/src/js/file1.js | 404 | http://www.foo.com/src/js/file1.js |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://foo.com/src/js/file2.js | 404 | http://www.foo.com/src/js/file2.js |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://geojson.org/geojson-spec.html#geometry-objects | 400 | http://geojson.org/geojson-spec.html#geometry-objects |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://geojson.org/geojson-spec.html#multipolygon | 400 | http://geojson.org/geojson-spec.html#multipolygon |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://github.com/substack/node-commondir.git | 404 | https://github.com/substack/node-commondir |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://google.com/doodle.png').pipe(fs.createWriteStream('doodle.png') | 404 | http://google.com/doodle.png%27%29.pipe%28fs.createWriteStream%28%27doodle.png%27%29 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://google.com/doodle.png').pipe(resp | 404 | http://google.com/doodle.png%27%29.pipe%28resp |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://google.com/img.png' | 404 | http://google.com/img.png%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://google.com/img.png').pipe(request.put('http://mysite.com/img.png') | 404 | http://google.com/img.png%27%29.pipe%28request.put%28%27http%3A//mysite.com/img.png%27%29 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://google.com/parse-things' | 404 | http://google.com/parse-things%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://heycam.github.io/webidl/#ecmascript-binding | 400 | http://heycam.github.io/webidl/#ecmascript-binding |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://heycam.github.io/webidl/#es-float | 400 | http://heycam.github.io/webidl/#es-float |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://heycam.github.io/webidl/#idl-boolean | 400 | http://heycam.github.io/webidl/#idl-boolean |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://heycam.github.io/webidl/#idl-types | 400 | http://heycam.github.io/webidl/#idl-types |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://heycam.github.io/webidl/#idl-unsigned-long | 400 | http://heycam.github.io/webidl/#idl-unsigned-long |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ieeexplore.ieee.org/servlet/opac?punumber=4610933 | 418 | https://ieeexplore.ieee.org/servlet/opac?punumber=4610933 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://img.badgesize.io/https://unpkg.com/react-composer/dist/react-composer.min.js?compression=gzip | 404 | https://img.badgesize.io/https://unpkg.com/react-composer/dist/react-composer.min.js?compression=gzip |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://individual-spec-membership.graphql.org/ | 404 | http://individual-spec-membership.graphql.org/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://json-schema.org/documentation.html | 404 | https://json-schema.org/documentation.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://json-schema.org/latest/json-schema-validation.html | 404 | https://json-schema.org/latest/json-schema-validation.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://jsperf.com/natural-sort-2/12 | 410 | https://jsperf.com/natural-sort-2/12 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://jsperf.com/object-json-stringify | 410 | https://jsperf.com/object-json-stringify |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://jsperf.com/sha3/4 | 410 | https://jsperf.com/sha3/4 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://jsperf.com/sha3/5 | 410 | https://jsperf.com/sha3/5 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://jsperf.com/string-concat-vs-pass-string-reference | 410 | https://jsperf.com/string-concat-vs-pass-string-reference |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://kangax.github.io/compat-table/es6/#test-Proxy | 400 | http://kangax.github.io/compat-table/es6/#test-Proxy |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://keepachangelog.com/)_ | 404 | https://keepachangelog.com/%29_ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://leveldb.org | 404 | http://leveldb.org |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://leveldb.org/img/badge.svg | 404 | http://leveldb.org/img/badge.svg |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost' | [Errno 11001] getaddrinfo failed | http://localhost' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:* | nonnumeric port: '*' | http://localhost:* |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:3000 | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:3000 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:3000' | nonnumeric port: '3000'' | http://localhost:3000' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:3000/ | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:3000/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:3000/@react-refresh | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:3000/@react-refresh |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:7936/contrib/copy-tex/index.html | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:7936/contrib/copy-tex/index.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8000/api/evaluation/assess | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8000/api/evaluation/assess |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8000/demo/ | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8000/demo/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8000/health | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8000/health |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8001 | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8001/api/v1/ai-assistant | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8001/api/v1/ai-assistant' | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8001/api/v1/ai-assistant/explain | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/explain |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8001/api/v1/ai-assistant/learning-advice | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/learning-advice |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8001/api/v1/ai-assistant/proof-hint | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/proof-hint |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8001/docs | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/docs |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8001/redoc | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/redoc |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localhost:8080 | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8080 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://lodash.com/docs#groupBy | 404 | https://lodash.com/docs%23groupBy |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://lodash.com/docs#transform | 404 | https://lodash.com/docs%23transform |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://math.arizona.edu/~cemela/spanish/content/workingpapers/UsingTwoLanguages.pdf | 404 | https://archive.math.arizona.edu/cemela/spanish/content/workingpapers/UsingTwoLanguages.pdf |
| `docs/11-高级数学/moduli-spaces.md` | http://math.mit.edu/~auroux/ | 404 | https://math.mit.edu/~auroux/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://math.mit.edu/~auroux/ | 404 | https://math.mit.edu/~auroux/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://math.mit.edu/~maulik/726/ | 404 | https://math.mit.edu/~maulik/726/ |
| `project/Harvard-232br-L4-定理对齐表.md` | http://math.mit.edu/~maulik/726/ | 404 | https://math.mit.edu/~maulik/726/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://math.mit.edu/~maulik/726/notes/lec15.pdf | 404 | https://math.mit.edu/~maulik/726/notes/lec15.pdf |
| `project/Harvard-232br-L4-定理对齐表.md` | http://math.mit.edu/~maulik/726/notes/lec15.pdf | 404 | https://math.mit.edu/~maulik/726/notes/lec15.pdf |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://math.mit.edu/~maulik/726/notes/lec18.pdf | 404 | https://math.mit.edu/~maulik/726/notes/lec18.pdf |
| `project/Harvard-232br-L4-定理对齐表.md` | http://math.mit.edu/~maulik/726/notes/lec18.pdf | 404 | https://math.mit.edu/~maulik/726/notes/lec18.pdf |
| `project/00-权威源复核清单.md` | http://math.stanford.edu/~vakil/216blog/FOAGoct2125public.pdf；已对齐 | 404 | http://math.stanford.edu/~vakil/216blog/FOAGoct2125public.pdf%EF%BC%9B%E5%B7%B2%E5%AF%B9%E9%BD%90 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://math.stanford.edu/~vakil/216blog/FOAGoct2125public.pdf；已对齐 | 404 | http://math.stanford.edu/~vakil/216blog/FOAGoct2125public.pdf%EF%BC%9B%E5%B7%B2%E5%AF%B9%E9%BD%90 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mysite.com/doodle.png' | 404 | http://mysite.com/doodle.png%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mysite.com/doodle.png')).pipe(resp | 404 | http://mysite.com/doodle.png%27%29%29.pipe%28resp |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mysite.com/doodle.png').pipe(resp | 404 | http://mysite.com/doodle.png%27%29.pipe%28resp |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mysite.com/img.png' | 404 | http://mysite.com/img.png%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mysite.com/img.png').then(function | 404 | http://mysite.com/img.png%27%29.then%28function |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mysite.com/obj.json' | 404 | http://mysite.com/obj.json%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://nginx | [Errno 11001] getaddrinfo failed | http://nginx |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://nodejs.org/api/' | 404 | http://nodejs.org/api/%27/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://nodejs.org/api/'/ | 404 | http://nodejs.org/api/%27/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://nodejs.org/images/logo.png' | 404 | https://nodejs.org/images/logo.png%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.anvaka.com/#/view/2d/inquirer | 400 | http://npm.anvaka.com/#%2Fview%2F2d%2Finquirer |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.anvaka.com/#/view/2d/prompts | 400 | http://npm.anvaka.com/#%2Fview%2F2d%2Fprompts |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://opensource.apple.com/source/ICU/ICU-400.42/icuSources/common/punycode.c | 404 | https://opensource.apple.com/source/ICU/ICU-400.42/icuSources/common/punycode.c |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://peterolson.github.io/BigInteger.js/benchmark/#Addition | 400 | http://peterolson.github.io/BigInteger.js/benchmark/#Addition |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://peterolson.github.io/BigInteger.js/benchmark/#Division | 400 | http://peterolson.github.io/BigInteger.js/benchmark/#Division |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://peterolson.github.io/BigInteger.js/benchmark/#Exponentiation | 400 | http://peterolson.github.io/BigInteger.js/benchmark/#Exponentiation |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://peterolson.github.io/BigInteger.js/benchmark/#Multiplication | 400 | http://peterolson.github.io/BigInteger.js/benchmark/#Multiplication |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://peterolson.github.io/BigInteger.js/benchmark/#Squaring | 400 | http://peterolson.github.io/BigInteger.js/benchmark/#Squaring |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://peterolson.github.io/BigInteger.js/benchmark/#Subtraction | 400 | http://peterolson.github.io/BigInteger.js/benchmark/#Subtraction |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://peterolson.github.io/BigInteger.js/benchmark/#toString | 400 | http://peterolson.github.io/BigInteger.js/benchmark/#toString |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://postcss.org/api/#container-error | 400 | http://postcss.org/api/#container-error |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://prometheus:9090/api/v1/status/targets | [Errno 11001] getaddrinfo failed | http://prometheus:9090/api/v1/status/targets |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://pyyaml.org/wiki/YAMLTagDiscussion | 404 | https://pyyaml.org/wiki/YAMLTagDiscussion |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://r.va.gg/2014/06/why-i-dont-use-nodes-core-stream-module.html).* | 404 | https://r.va.gg/2014/06/why-i-dont-use-nodes-core-stream-module.html%29.%2A |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ro.me | 404 | http://ro.me |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://stylelint.io/)** | 404 | https://stylelint.io/%29%2A%2A |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://tc39.github.io/ecmascript-asyncawait/ | 404 | https://tc39.es/ecmascript-asyncawait/ |
| `docs/11-高级数学/40-量子计算数学基础.md` | http://theory.caltech.edu/~preskill/ph219/ | 404 | https://www.theory.caltech.edu/~preskill/ph219 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://theory.caltech.edu/~preskill/ph219/ | 404 | https://www.theory.caltech.edu/~preskill/ph219 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://unix:/absolute/path/to/unix.socket:/request/path' | [Errno 11001] getaddrinfo failed | http://unix:/absolute/path/to/unix.socket:/request/path' |
| `concept/核心概念/31-算法.md` | http://us.metamath.org/mpeuni/df-algorithm.html | 404 | https://us.metamath.org/mpeuni/df-algorithm.html |
| `concept/核心概念/27-同余.md` | http://us.metamath.org/mpeuni/df-congruence.html | 404 | https://us.metamath.org/mpeuni/df-congruence.html |
| `concept/核心概念/20-曲率.md` | http://us.metamath.org/mpeuni/df-curvature.html | 404 | https://us.metamath.org/mpeuni/df-curvature.html |
| `concept/核心概念/29-图.md` | http://us.metamath.org/mpeuni/df-graph.html | 404 | https://us.metamath.org/mpeuni/df-graph.html |
| `concept/核心概念/25-同调.md` | http://us.metamath.org/mpeuni/df-homology.html | 404 | https://us.metamath.org/mpeuni/df-homology.html |
| `concept/核心概念/24-同伦.md` | http://us.metamath.org/mpeuni/df-homotopy.html | 404 | https://us.metamath.org/mpeuni/df-homotopy.html |
| `concept/核心概念/33-朗兰兹纲领.md` | http://us.metamath.org/mpeuni/df-langlands.html | 404 | https://us.metamath.org/mpeuni/df-langlands.html |
| `concept/核心概念/28-L函数.md` | http://us.metamath.org/mpeuni/df-lfunction.html | 404 | https://us.metamath.org/mpeuni/df-lfunction.html |
| `concept/核心概念/18-流形.md` | http://us.metamath.org/mpeuni/df-manifold.html | 404 | https://us.metamath.org/mpeuni/df-manifold.html |
| `concept/核心概念/32-表示.md` | http://us.metamath.org/mpeuni/df-representation.html | 404 | https://us.metamath.org/mpeuni/df-representation.html |
| `concept/核心概念/19-黎曼流形.md` | http://us.metamath.org/mpeuni/df-riemann.html | 404 | https://us.metamath.org/mpeuni/df-riemann.html |
| `concept/核心概念/21-概形.md` | http://us.metamath.org/mpeuni/df-scheme.html | 404 | https://us.metamath.org/mpeuni/df-scheme.html |
| `concept/核心概念/22-层.md` | http://us.metamath.org/mpeuni/df-sheaf.html | 404 | https://us.metamath.org/mpeuni/df-sheaf.html |
| `docs/11-高级数学/random-matrix-theory.md` | http://www.brunel.ac.uk/randommatrix/ | 404 | https://www.brunel.ac.uk/randommatrix |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://www.foo.com/src | 404 | http://www.foo.com/src |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://www.foo.com/src',url='foo.min.js.map' | 404 | http://www.foo.com/src%27%2Curl%3D%27foo.min.js.map%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://www.foo.com/src/js/file1.js | 404 | http://www.foo.com/src/js/file1.js |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://www.foo.com/src/js/file2.js | 404 | http://www.foo.com/src/js/file2.js |
| `数学家理念体系/00-ONLINE-RESOURCES-ALIGNMENT.md` | http://www.numdam.org/numdam-bin/recherche?au=Grothendieck | 404 | https://www.numdam.org/numdam-bin/recherche?au=Grothendieck |
| `docs/链接维护指南.md` | https:// | no host given | https:// |
| `docs/管理员手册/05-安全管理.md` | https://$server_name$request_uri | [Errno 11001] getaddrinfo failed | https://$server_name$request_uri |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://2ality.com/2017/05/regexp-lookbehind-assertions.html | 404 | https://2ality.com/2017/05/regexp-lookbehind-assertions.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://2ality.com/2017/05/regexp-named-capture-groups.html | 404 | https://2ality.com/2017/05/regexp-named-capture-groups.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://abc.com/~smith/home.html | 404 | https://abc.com/~smith/home.html |
| `数学家理念体系/00-ONLINE-RESOURCES-ALIGNMENT.md` | https://agrothendieck.github.io/ | 404 | https://agrothendieck.github.io/ |
| `docs/11-高级数学/random-matrix-theory.md` | https://aimpl.org/randommatrix/ | 404 | https://aimpl.org/randommatrix/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://archive.math.arizona.edu/cemela/spanish/content/workingpapers/UsingTwoLanguages.pdf | 404 | https://archive.math.arizona.edu/cemela/spanish/content/workingpapers/UsingTwoLanguages.pdf |
| `数学家理念体系/00-ONLINE-RESOURCES-ALIGNMENT.md` | https://archive.org/details/disquisitionesa00gausgoog | 404 | https://archive.org/details/disquisitionesa00gausgoog |
| `docs/12-学术资源/16-Terence-Tao博客精华整理.md` | https://arxiv.org/a/tao_t_1 | 404 | https://arxiv.org/a/tao_t_1.html |
| `docs/00-指南与FAQ/用户指南/02-新手入门指南.md` | https://arxiv.org/math | 404 | https://arxiv.org/math |
| `docs/新手入门指南.md` | https://arxiv.org/math | 404 | https://arxiv.org/math |
| `docs/11-高级数学/32-量子数学-深化版.md` | https://blog.google/technology/ai/quantum-ai/ | 404 | https://blog.google/technology/ai/quantum-ai/ |
| `project/00-项目全面批判性评价与改进计划-2025年11月30日.md` | https://blog.sina.com.cn/s/blog_635affba0100gfvp.html | 418 | https://blog.sina.com.cn/s/blog_635affba0100gfvp.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://browsenpm.org/ | 404 | https://browsenpm.org/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://browserify.org/)/ | 404 | https://browserify.org/%29/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://cssinjs.org/)** | 404 | https://cssinjs.org/%29%2A%2A |
| `docs/10-应用数学/01-核心内容/信息论-香农编码定理-深度扩展.md` | https://doi.org/10.1002/j.1538-7305.1948.tb01338.x | 418 | https://ieeexplore.ieee.org/document/6773024 |
| `concept/view/07-国际数学教育研究/03-新加坡数学教育/03-新加坡数学教育.md` | https://doi.org/10.1007/s10763-009-9173-4 | 404 | https://doi.org/10.1007/s10763-009-9173-4 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://donavon.com/ | 404 | https://donavon.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://drafts.csswg.org/selectors4/ | 404 | https://drafts.csswg.org/selectors4/ |
| `docs/08-计算数学/00-国际课程对齐对照表.md` | https://ee364a.github.io/ | 404 | https://ee364a.github.io/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://eslint.org/docs/latest/extend/working-with-plugins%23environments-in-plugins | 404 | https://eslint.org/docs/latest/extend/working-with-plugins%23environments-in-plugins |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://eslint.org/docs/latest/extend/working-with-plugins%23environments-in-plugins%29.%2A%2A | 404 | https://eslint.org/docs/latest/extend/working-with-plugins%23environments-in-plugins%29.%2A%2A |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://eslint.org/doctrine/demo/ | 404 | https://eslint.org/doctrine/demo/ |
| `docs/09-形式化证明/00-形式化证明完成报告.md` | https://formalmath.github.io/ | 404 | https://formalmath.github.io/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://gist.githubusercontent.com/mbostock/raw/4343214/thumbnail.png | 400 | https://gist.githubusercontent.com/mbostock/raw/4343214/thumbnail.png |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://gist.githubusercontent.com/mbostock/raw/9078690/thumbnail.png | 400 | https://gist.githubusercontent.com/mbostock/raw/9078690/thumbnail.png |
| `docs/00-快速开始指南.en.md` | https://github.com/FormalMath/FormalMath | 404 | https://github.com/FormalMath/FormalMath |
| `docs/00-快速开始指南.md` | https://github.com/FormalMath/FormalMath | 404 | https://github.com/FormalMath/FormalMath |
| `docs/00-指南与FAQ/用户指南/02-新手入门指南.md` | https://github.com/FormalMath/FormalMath | 404 | https://github.com/FormalMath/FormalMath |
| `docs/新手入门指南.md` | https://github.com/FormalMath/FormalMath | 404 | https://github.com/FormalMath/FormalMath |
| `docs/00-指南与FAQ/用户指南/02-新手入门指南.md` | https://github.com/FormalMath/FormalMath.git | 404 | https://github.com/FormalMath/FormalMath |
| `docs/新手入门指南.md` | https://github.com/FormalMath/FormalMath.git | 404 | https://github.com/FormalMath/FormalMath |
| `docs/00-快速开始指南.en.md` | https://github.com/FormalMath/FormalMath/issues | 404 | https://github.com/FormalMath/FormalMath/issues |
| `docs/00-快速开始指南.md` | https://github.com/FormalMath/FormalMath/issues | 404 | https://github.com/FormalMath/FormalMath/issues |
| `docs/CI_CD指南.md` | https://github.com/FormalMath/discussions | 404 | https://github.com/FormalMath/discussions |
| `docs/CI_CD指南.md` | https://github.com/FormalMath/issues/new | 404 | https://github.com/FormalMath/issues/new |
| `docs/00-指南与FAQ/用户指南/02-新手入门指南.md` | https://github.com/YOUR_USERNAME/FormalMath.git | 404 | https://github.com/YOUR_USERNAME/FormalMath |
| `docs/新手入门指南.md` | https://github.com/YOUR_USERNAME/FormalMath.git | 404 | https://github.com/YOUR_USERNAME/FormalMath |
| `docs/09-形式化证明/00-从FormalMath到Mathlib4学习路径.md` | https://github.com/YOUR_USERNAME/mathlib4.git | 404 | https://github.com/YOUR_USERNAME/mathlib4 |
| `docs/开发文档/README.md` | https://github.com/formalmath/FormalMath | 404 | https://github.com/formalmath/FormalMath |
| `docs/开发文档/03-前端开发指南.md` | https://github.com/formalmath/FormalMath.git | 404 | https://github.com/formalmath/FormalMath |
| `docs/开发文档/06-贡献指南.md` | https://github.com/formalmath/FormalMath.git | 404 | https://github.com/formalmath/FormalMath |
| `docs/09-形式化证明/00-形式化证明完成报告.md` | https://github.com/formalmath/formalmath | 404 | https://github.com/formalmath/formalmath |
| `docs/09-形式化证明/Lean4/INDEX.md` | https://github.com/formalmath/formalmath | 404 | https://github.com/formalmath/formalmath |
| `docs/decision-trees/00-决策树使用指南.md` | https://github.com/formalmath/issues | 404 | https://github.com/formalmath/issues |
| `docs/13-数学前沿/05-同伦类型论导论.md` | https://github.com/leanprover-community/lean-hott | 404 | https://github.com/leanprover-community/lean-hott |
| `docs/09-形式化证明/形式化证明与AI.md` | https://github.com/leanprover-community/lean4-copilot | 404 | https://github.com/leanprover-community/lean4-copilot |
| `数学家理念体系/冯诺依曼数学理念/02-博弈论与极小极大定理.md` | https://github.com/leanprover-community/mathlib4)。Mathlib4 | 404 | https://github.com/leanprover-community/mathlib4%29%E3%80%82Mathlib4 |
| `docs/02-代数结构/07-项目文档/项目总览/项目启动执行指南.md` | https://github.com/leanprover/elan/releases/latest/download/elan-init.sh | 404 | https://github.com/leanprover/elan/releases/download/v4.2.3/elan-init.sh |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://github.com/substack/node-commondir.git | 404 | https://github.com/substack/node-commondir |
| `docs/管理员手册/02-部署指南.md` | https://github.com/username/FormalMath.git | 404 | https://github.com/username/FormalMath |
| `docs/管理员手册/04-故障排除.md` | https://github.com/username/FormalMath.git | 404 | https://github.com/username/FormalMath |
| `docs/管理员手册/06-备份恢复.md` | https://github.com/username/FormalMath.git | 404 | https://github.com/username/FormalMath |
| `docs/用户手册/04-常见问题解答.md` | https://github.com/xxx/FormalMath.git | 404 | https://github.com/xxx/FormalMath |
| `docs/用户手册/用户手册-合并版.md` | https://github.com/xxx/FormalMath.git | 404 | https://github.com/xxx/FormalMath |
| `docs/02-代数结构/07-项目文档/项目总览/项目启动执行指南.md` | https://github.com/your-org/formalmath.git | 404 | https://github.com/your-org/formalmath |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://ieeexplore.ieee.org/servlet/opac?punumber=4610933 | 418 | https://ieeexplore.ieee.org/servlet/opac?punumber=4610933 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://json-schema.org/documentation.html | 404 | https://json-schema.org/documentation.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://json-schema.org/latest/json-schema-validation.html | 404 | https://json-schema.org/latest/json-schema-validation.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://jsperf.com/natural-sort-2/12 | 410 | https://jsperf.com/natural-sort-2/12 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://jsperf.com/object-json-stringify | 410 | https://jsperf.com/object-json-stringify |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://jsperf.com/sha3/4 | 410 | https://jsperf.com/sha3/4 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://jsperf.com/sha3/5 | 410 | https://jsperf.com/sha3/5 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://jsperf.com/string-concat-vs-pass-string-reference | 410 | https://jsperf.com/string-concat-vs-pass-string-reference |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://keepachangelog.com/)_ | 404 | https://keepachangelog.com/%29_ |
| `docs/09-形式化证明/00-Mathlib4概念映射索引.md` | https://lean-lang.org/doc/ | 404 | https://lean-lang.org/doc/ |
| `docs/09-形式化证明/00-README.md` | https://lean-lang.org/doc/ | 404 | https://lean-lang.org/doc/ |
| `docs/09-形式化证明/00-从FormalMath到Mathlib4学习路径.md` | https://lean-lang.org/doc/ | 404 | https://lean-lang.org/doc/ |
| `docs/09-形式化证明/Lean4教程/03-Mathlib4使用指南.md` | https://leanprover-community.github.io/contribute/index.html)**：了解编码风格、命名约定、PR | 404 | https://leanprover-community.github.io/contribute/index.html%29%2A%2A%EF%BC%9A%E4%BA%86%E8%A7%A3%E7%BC%96%E7%A0%81%E9%A3%8E%E6%A0%BC%E3%80%81%E5%91%BD%E5%90%8D%E7%BA%A6%E5%AE%9A%E3%80%81PR |
| `docs/09-形式化证明/Lean4教程/03-Mathlib4使用指南.md` | https://leanprover-community.github.io/contribute/style.html)**： | 404 | https://leanprover-community.github.io/contribute/style.html%29%2A%2A%EF%BC%9A |
| `docs/00-2025年数学前沿进展综述.md` | https://leanprover-community.github.io/flt/ | 404 | https://leanprover-community.github.io/flt/ |
| `docs/02-代数结构/07-项目文档/项目总览/抽象代数结构全面分析计划-2025年1月.md` | https://leanprover-community.github.io/mathlib4/ | 404 | https://leanprover-community.github.io/mathlib4/ |
| `docs/13-数学前沿/07-导出范畴入门.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/ | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/ |
| `docs/02-代数结构/02-核心理论/群论/定理证明/拉格朗日定理-完整证明.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Subgroup/Basic.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/Subgroup/Basic.html |
| `docs/00-知识图谱/形式化-Lean4定理映射图.md` | https://leanprover.github.io/lean4/doc/ | 404 | https://leanprover.github.io/lean4/doc/ |
| `docs/02-代数结构/02-核心理论/代数几何/Lean4形式化实现-代数几何.md` | https://leanprover.github.io/lean4/doc/ | 404 | https://leanprover.github.io/lean4/doc/ |
| `docs/09-形式化证明/00-Lean4形式化证明库状态.md` | https://leanprover.github.io/lean4/doc/ | 404 | https://leanprover.github.io/lean4/doc/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://lodash.com/docs%23groupBy | 404 | https://lodash.com/docs%23groupBy |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://lodash.com/docs%23transform | 404 | https://lodash.com/docs%23transform |
| `docs/11-高级数学/derived-algebraic-geometry.md` | https://math.berkeley.edu/~arinkin/ | 404 | https://math.berkeley.edu/~arinkin/ |
| `docs/11-高级数学/sheaf-cohomology.md` | https://math.berkeley.edu/~arinkin/ | 404 | https://math.berkeley.edu/~arinkin/ |
| `project/ETH-Zurich-course-mapping-detailed.md` | https://math.ethz.ch/studium/studiengaenge/bachelor.html | 404 | https://math.ethz.ch/studium/studiengaenge/bachelor.html |
| `docs/11-高级数学/derived-algebraic-geometry.md` | https://math.mit.edu/research/pure/applied-sem-future.html | 404 | https://math.mit.edu/research/pure/applied-sem-future.html |
| `docs/00-推理判断树/05-数论完整推理树.md` | https://math.mit.edu/research/pure/applied.html | 404 | https://math.mit.edu/research/pure/applied.html |
| `project/00-权威源年度复核报告-2026年4月.md` | https://math.mit.edu/research/pure/applied.html | 404 | https://math.mit.edu/research/pure/applied.html |
| `project/MIT-course-mapping-detailed.md` | https://math.mit.edu/research/pure/applied.html | 404 | https://math.mit.edu/research/pure/applied.html |
| `docs/11-高级数学/intersection-theory.md` | https://math.mit.edu/~abrahmc/ | 404 | https://math.mit.edu/~abrahmc/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://math.mit.edu/~auroux/ | 404 | https://math.mit.edu/~auroux/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://math.mit.edu/~maulik/726/ | 404 | https://math.mit.edu/~maulik/726/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://math.mit.edu/~maulik/726/notes/lec15.pdf | 404 | https://math.mit.edu/~maulik/726/notes/lec15.pdf |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://math.mit.edu/~maulik/726/notes/lec18.pdf | 404 | https://math.mit.edu/~maulik/726/notes/lec18.pdf |
| `project/v2-quality-rewrite/deliverables/D002-semantic-alignment-playbook.md` | https://math.mit.edu/~rodriguez/18.100A/ | 404 | https://math.mit.edu/~rodriguez/18.100A/ |
| `docs/concept-mindmaps/14-诺特环-思维导图.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `docs/inference-trees/08-诺特环升链条件.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `docs/visualizations/概念/代数结构/14-诺特环.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/00-归档-2026年4月-其他数学家/诺特数学理念/08-知识关联分析/01-概念关联网络.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/00-归档-2026年4月-其他数学家/诺特数学理念/08-知识关联分析/02-理论关联图谱.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/00-归档-2026年4月-其他数学家/诺特数学理念/08-知识关联分析/03-跨学科关联.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/外尔数学理念/06-对比研究/02-与诺特的对比.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/戴德金数学理念/06-对比研究/03-与诺特的对比.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/01-核心理论/01-抽象代数哲学与方法论.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/01-核心理论/02-诺特定理与对称性.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/01-核心理论/05-同调代数方法论.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/01-抽象代数/01-诺特环与理想理论.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/01-抽象代数贡献/04-诺特环与诺特模.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/01-抽象代数贡献/08-群论贡献.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/02-代数几何贡献/02-希尔伯特-诺特定理.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/02-诺特定理/01-诺特定理数学表述.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/03-代数几何/01-诺特正规化与代数几何基础.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/04-表示论/01-表示论贡献.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/05-其他数学贡献/01-物理中的对称性.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/05-其他数学贡献/02-变分法中的对称性.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/05-其他数学贡献/03-计算数学方法.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/05-其他数学贡献/04-数学教育方法.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/02-数学内容深度分析/05-其他数学贡献/05-跨学科应用.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/诺特数学理念/03-教育与影响/01-教育理念与方法.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/肖尔策数学理念/02-数学内容深度分析/01-完美oid空间.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ |
| `数学家理念体系/00-归档-2026年4月-其他数学家/巴拿赫数学理念/06-对比研究/02-与冯诺依曼的对比.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/冯诺依曼数学理念/01-冯诺依曼代数基础.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/冯诺依曼数学理念/02-数学内容深度分析/01-算子理论/02-冯诺依曼代数理论.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/冯诺依曼数学理念/03-冯诺依曼计算机架构的数学原理.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/冯诺依曼数学理念/05-冯诺依曼与信息论萌芽.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/冯诺依曼数学理念/冯诺依曼-与信息论萌芽.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/冯诺依曼数学理念/冯诺依曼-冯诺依曼代数基础.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/冯诺依曼数学理念/冯诺依曼-博弈论与极小极大定理.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/冯诺依曼数学理念/冯诺依曼-计算机架构的数学原理.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `数学家理念体系/戴德金数学理念/01-核心理论/04-数学严格性思想.md` | https://mathshistory.st-andrews.ac.uk/HistTopics/Arithmetization_of_analysis/ | 404 | https://mathshistory.st-andrews.ac.uk/HistTopics/Arithmetization_of_analysis/ |
| `docs/07-数理逻辑/01-基础内容/05-多值逻辑.md` | https://mathworld.wolfram.com/Many-ValuedLogic.html | 404 | https://mathworld.wolfram.com/Many-ValuedLogic.html |
| `docs/08-计算数学/03-优化算法.md` | https://mathworld.wolfram.com/Optimization.html | 404 | https://mathworld.wolfram.com/Optimization.html |
| `docs/08-计算数学/04-并行计算.md` | https://mathworld.wolfram.com/ParallelAlgorithm.html | 404 | https://mathworld.wolfram.com/ParallelAlgorithm.html |
| `docs/08-计算数学/05-符号计算.md` | https://mathworld.wolfram.com/SymbolicComputation.html | 404 | https://mathworld.wolfram.com/SymbolicComputation.html |
| `docs/11-高级数学/nLab-金层对齐/01-无穷一范畴基础.md` | https://ncatlab.org/nlab/show/%28infinity%2C1%29-category)）。一个 | 404 | https://ncatlab.org/nlab/show/%28infinity%2C1%29-category%29%EF%BC%89%E3%80%82%E4%B8%80%E4%B8%AA |
| `docs/11-高级数学/nLab-金层对齐/01-无穷一范畴基础.md` | https://ncatlab.org/nlab/show/%28infinity%2C1%29-category)）。这一概念最早可以追溯到 | 404 | https://ncatlab.org/nlab/show/%28infinity%2C1%29-category%29%EF%BC%89%E3%80%82%E8%BF%99%E4%B8%80%E6%A6%82%E5%BF%B5%E6%9C%80%E6%97%A9%E5%8F%AF%E4%BB%A5%E8%BF%BD%E6%BA%AF%E5%88%B0 |
| `docs/11-高级数学/nLab-金层对齐/01-无穷一范畴基础.md` | https://ncatlab.org/nlab/show/Kan+complex)）。对 | 404 | https://ncatlab.org/nlab/show/Kan%2Bcomplex%29%EF%BC%89%E3%80%82%E5%AF%B9 |
| `docs/13-代数几何/定理证明/Riemann-Roch定理-曲线-完整证明.md` | https://ncatlab.org/nlab/show/Riemann-Roch+theorem | 404 | https://ncatlab.org/nlab/show/Riemann-Roch%2Btheorem |
| `docs/03-分析学/01-实分析/定理证明/Rolle定理-完整证明.md` | https://ncatlab.org/nlab/show/Rolle+theorem | 404 | https://ncatlab.org/nlab/show/Rolle%2Btheorem |
| `concept/04-认知工具/概念卡片/Sylow第一定理.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/00-习题示例反例库/代数/ALG-008-Sylow第一定理的应用.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/00-工作示例库/02-代数结构/10-Sylow定理应用-工作示例.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/00-工作示例库/02-代数结构/13-Sylow第一定理-工作示例.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/00-工作示例库/13-Sylow第一定理-工作示例.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/00-核心概念理解三问/11-核心定理多表征/38-Sylow定理-五种表征.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/00-知识层次体系/L2-定理证明层/代数/02-Sylow定理.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/00-银层核心课程/MIT-18.701-抽象代数/Sylow第一定理.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/02-代数结构/02-核心理论/MIT-18.701/03-Sylow第一定理.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/02-代数结构/02-核心理论/群论/定理证明/Sylow第一定理-完整证明.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/09-形式化证明/双语对照/Sylow第一定理-自然语言与Lean4对照.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/concept-mindmaps/05-Sylow定理-思维导图.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/decision-trees/16-Sylow定理应用决策.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/inference-trees/02-Sylow定理完整证明树.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/visualizations/思维导图/概念/Sylow定理.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/visualizations/思维导图/概念/代数学/Sylow定理.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `docs/visualizations/概念/代数结构/13-西罗定理结构.md` | https://ncatlab.org/nlab/show/Sylow+theorem | 404 | https://ncatlab.org/nlab/show/Sylow%2Btheorem |
| `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/03-上同调理论/03-韦伊猜想的证明.md` | https://ncatlab.org/nlab/show/Weil+conjecture | 404 | https://ncatlab.org/nlab/show/Weil%2Bconjecture |
| `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/02-概形理论/03-纤维积与基变化.md` | https://ncatlab.org/nlab/show/fiber+product | 404 | https://ncatlab.org/nlab/show/fiber%2Bproduct |
| `docs/11-高级数学/nLab-金层对齐/02-Topos理论的范畴观点.md` | https://ncatlab.org/nlab/show/geometric+morphism)）。设 | 404 | https://ncatlab.org/nlab/show/geometric%2Bmorphism%29%EF%BC%89%E3%80%82%E8%AE%BE |
| `数学家理念体系/嘉当数学理念/01-活动标架法教学级阐述.md` | https://ncatlab.org/nlab/show/moving+frame | 404 | https://ncatlab.org/nlab/show/moving%2Bframe |
| `数学家理念体系/嘉当数学理念/02-数学内容深度分析.md` | https://ncatlab.org/nlab/show/moving+frame | 404 | https://ncatlab.org/nlab/show/moving%2Bframe |
| `数学家理念体系/嘉当数学理念/嘉当-活动标架法教学级阐述.md` | https://ncatlab.org/nlab/show/moving+frame | 404 | https://ncatlab.org/nlab/show/moving%2Bframe |
| `docs/00-习题示例反例库/PDE-波动热Laplace方程-习题集.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/00-习题示例反例库/实分析/ANA-148-偏微分方程.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/00-习题示例反例库/实分析/ANA-198-偏微分方程进阶.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/00-习题示例反例库/实分析/ANA-199-几何偏微分方程.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/00-习题示例反例库/微分方程/DE-011-025-偏微分方程.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/00-知识图谱/知识图谱-025-偏微分方程分类图谱.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/00-知识层次体系/L3-理论建构层/02-分析方向/04-偏微分方程理论.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/00-表征实例库/表征实例-054-偏微分方程的适定性理论.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/03-分析学/06-偏微分方程/01-偏微分方程核心-深度扩展版.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/03-分析学/06-偏微分方程/偏微分方程基础-深度版.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/03-分析学/偏微分方程高级主题-简介.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/08-计算数学/09-偏微分方程数值解.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/08-计算数学/偏微分方程数值解-深度版.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/10-应用数学/supplement/02-偏微分方程基础-波动与热传导.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/10-应用数学/偏微分方程-习题与数值解.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/concept-mindmaps/num-07-偏微分方程数值解.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `数学家理念体系/00-归档-2026年4月-其他数学家/庞加莱数学理念/02-数学内容深度分析/05-数学物理/08-流体力学.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `数学家理念体系/00-归档-2026年4月-其他数学家/庞加莱数学理念/02-数学内容深度分析/05-数学物理/25-流体力学中的数学方法.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `数学家理念体系/希尔伯特数学理念/02-数学内容深度分析/06-其他数学贡献/02-变分法与偏微分方程.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `数学家理念体系/希尔伯特数学理念/02-数学内容深度分析/06-其他数学贡献/11-偏微分方程理论与应用.md` | https://ncatlab.org/nlab/show/partial+differential+equation | 404 | https://ncatlab.org/nlab/show/partial%2Bdifferential%2Bequation |
| `docs/11-高级数学/nLab-金层对齐/01-无穷一范畴基础.md` | https://ncatlab.org/nlab/show/quasi-category)）。一个单纯集 | 404 | https://ncatlab.org/nlab/show/quasi-category%29%EF%BC%89%E3%80%82%E4%B8%80%E4%B8%AA%E5%8D%95%E7%BA%AF%E9%9B%86 |
| `docs/11-高级数学/nLab-金层对齐/02-Topos理论与SGA4.md` | https://ncatlab.org/nlab/show/sheaf+topos | 404 | https://ncatlab.org/nlab/show/sheaf%2Btopos |
| `docs/11-高级数学/nLab-金层对齐/02-Topos理论的范畴观点.md` | https://ncatlab.org/nlab/show/sheaf+topos | 404 | https://ncatlab.org/nlab/show/sheaf%2Btopos |
| `docs/11-高级数学/nLab-金层对齐/02-Topos理论的范畴观点.md` | https://ncatlab.org/nlab/show/sheaf+topos)）。设 | 404 | https://ncatlab.org/nlab/show/sheaf%2Btopos%29%EF%BC%89%E3%80%82%E8%AE%BE |
| `docs/11-高级数学/nLab-金层对齐/01-无穷一范畴基础.md` | https://ncatlab.org/nlab/show/simplicial+set)；Eilenberg–Zilber | 404 | https://ncatlab.org/nlab/show/simplicial%2Bset%29%EF%BC%9BEilenberg%E2%80%93Zilber |
| `数学家理念体系/格洛腾迪克数学理念/金层重构/G5-标准猜想与Motive理论.md` | https://ncatlab.org/nlab/show/standard+conjectures | 404 | https://ncatlab.org/nlab/show/standard%2Bconjectures |
| `docs/00-习题示例反例库/几何/GEO-002-切空间与切丛.md` | https://ncatlab.org/nlab/show/tangent+space | 404 | https://ncatlab.org/nlab/show/tangent%2Bspace |
| `docs/00-表征实例库/表征实例-032-代数簇的维数定义对比.md` | https://ncatlab.org/nlab/show/tangent+space | 404 | https://ncatlab.org/nlab/show/tangent%2Bspace |
| `docs/04-几何与拓扑/02-微分几何-扩展/03-切空间与向量场.md` | https://ncatlab.org/nlab/show/tangent+space | 404 | https://ncatlab.org/nlab/show/tangent%2Bspace |
| `docs/13-代数几何/习题/AG-EX-008-切空间与光滑性.md` | https://ncatlab.org/nlab/show/tangent+space | 404 | https://ncatlab.org/nlab/show/tangent%2Bspace |
| `docs/14-微分几何/02-切空间与切向量.md` | https://ncatlab.org/nlab/show/tangent+space | 404 | https://ncatlab.org/nlab/show/tangent%2Bspace |
| `docs/concept-mindmaps/dg-tangent-space.md` | https://ncatlab.org/nlab/show/tangent+space | 404 | https://ncatlab.org/nlab/show/tangent%2Bspace |
| `docs/visualizations/思维导图/概念/切空间.md` | https://ncatlab.org/nlab/show/tangent+space | 404 | https://ncatlab.org/nlab/show/tangent%2Bspace |
| `docs/11-高级数学/nLab-金层对齐/02-Topos理论的范畴观点.md` | https://ncatlab.org/nlab/show/topos)）。一个**初等 | 404 | https://ncatlab.org/nlab/show/topos%29%EF%BC%89%E3%80%82%E4%B8%80%E4%B8%AA%2A%2A%E5%88%9D%E7%AD%89 |
| `docs/00-习题示例反例库/实分析/ANA-006-一致连续性的判定.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `docs/00-习题示例反例库/实分析/ANA-023-一致连续性证明.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `docs/00-习题示例反例库/实分析/ANA-027-一致连续性的运算.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `docs/00-银层核心课程/MIT-18.100A-实分析/一致连续性定理.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `docs/03-分析学/01-实分析/MIT-18.100A/03-一致连续性.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `docs/03-分析学/supplement/04-连续性与一致连续性-MIT18.100A对齐.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `docs/09-形式化证明/双语对照/一致连续性-Heine-Cantor定理-自然语言与Lean4对照.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `docs/inference-trees/03-continuity-equicontinuity.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `docs/visualizations/思维导图/概念/一致连续.md` | https://ncatlab.org/nlab/show/uniform+continuity | 404 | https://ncatlab.org/nlab/show/uniform%2Bcontinuity |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://nodejs.org/images/logo.png' | 404 | https://nodejs.org/images/logo.png%27 |
| `docs/00-贡献者指南/银层文档标准模板.md` | https://ocw.mit.edu/... | 404 | https://ocw.mit.edu/.../ |
| `数学家理念体系/欧拉数学理念/01-欧拉公式与复分析的严格证明.md` | https://ocw.mit.edu/courses/18-04-complex-variables-with-applications-fall-2020/ | 404 | https://ocw.mit.edu/courses/18-04-complex-variables-with-applications-fall-2020/ |
| `project/MIT-18.701-语义级对齐手册.md` | https://ocw.mit.edu/courses/18-701-algebra-i-fall-2021/ | 404 | https://ocw.mit.edu/courses/18-701-algebra-i-fall-2021/ |
| `project/00-权威源复核清单.md` | https://ocw.mit.edu/courses/18-705-commutative-algebra-fall-2008/；2025-26 | 404 | https://ocw.mit.edu/courses/18-705-commutative-algebra-fall-2008/%EF%BC%9B2025-26/ |
| `docs/04-几何与拓扑/01-几何学基础/03-微分几何.md` | https://ocw.mit.edu/courses/18-950-differential-geometry-fall-2006/ | 404 | https://ocw.mit.edu/courses/18-950-differential-geometry-fall-2006/ |
| `数学家理念体系/高斯数学理念/02-高斯曲率与内蕴几何.md` | https://ocw.mit.edu/courses/18-950-differential-geometry-fall-2020/ | 404 | https://ocw.mit.edu/courses/18-950-differential-geometry-fall-2020/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://opensource.apple.com/source/ICU/ICU-400.42/icuSources/common/punycode.c | 404 | https://opensource.apple.com/source/ICU/ICU-400.42/icuSources/common/punycode.c |
| `project/v2-quality-rewrite/workspaces/courses/harvard-232br/T009-syllabus-deconstruction/task-report.md` | https://people.maths.ox.ac.uk/liu/notes/s17-algebraic-geometry.pdf | 404 | https://people.maths.ox.ac.uk/liu/notes/s17-algebraic-geometry.pdf |
| `数学家理念体系/哥德尔数学理念/02-数学内容深度分析/02-可构造宇宙/01-可构造宇宙的定义.md` | https://plato.stanford.edu/entries/constructibility/ | 404 | https://plato.stanford.edu/entries/constructibility/ |
| `数学家理念体系/戴德金数学理念/01-核心理论/04-数学严格性思想.md` | https://plato.stanford.edu/entries/continuum/ | 404 | https://plato.stanford.edu/entries/continuum/ |
| `docs/07-数理逻辑/01-基础内容/00-README.md` | https://plato.stanford.edu/entries/logic/ | 404 | https://plato.stanford.edu/entries/logic/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://pyyaml.org/wiki/YAMLTagDiscussion | 404 | https://pyyaml.org/wiki/YAMLTagDiscussion |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://r.va.gg/2014/06/why-i-dont-use-nodes-core-stream-module.html).* | 404 | https://r.va.gg/2014/06/why-i-dont-use-nodes-core-stream-module.html%29.%2A |
| `docs/管理员手册/应急预案.md` | https://raw.githubusercontent.com/formalmath/tools/main/collect_logs.sh | 404 | https://raw.githubusercontent.com/formalmath/tools/main/collect_logs.sh |
| `docs/管理员手册/应急预案.md` | https://raw.githubusercontent.com/formalmath/tools/main/emergency_backup.sh | 404 | https://raw.githubusercontent.com/formalmath/tools/main/emergency_backup.sh |
| `docs/管理员手册/应急预案.md` | https://raw.githubusercontent.com/formalmath/tools/main/quick_diag.sh | 404 | https://raw.githubusercontent.com/formalmath/tools/main/quick_diag.sh |
| `docs/12-学术资源/18-数学科普视频资源索引.md` | https://space.bilibili.com/88461692 | 412 | https://space.bilibili.com/88461692 |
| `project/00-国际课程与机构对齐对照表-2026年2月.md` | https://stacks.math.columbia.edu/* | 404 | https://stacks.math.columbia.edu/%2A |
| `project/00-国际课程与机构对齐对照表-2026年4月.md` | https://stacks.math.columbia.edu/* | 404 | https://stacks.math.columbia.edu/%2A |
| `docs/15-同调代数/13-Leray谱序列.md` | https://stacks.math.columbia.edu/tag/013M | 404 | https://stacks.math.columbia.edu/tag/013M |
| `project/00-FormalMath三层内容标准-v2.0.md` | https://stacks.math.columbia.edu/tag/XXXX | 404 | https://stacks.math.columbia.edu/tag/XXXX |
| `project/00-项目进度报告/Phase1-全面推进-Frontmatter修复与银层元数据对齐报告.md` | https://stacks.math.columbia.edu/tag/XXXX | 404 | https://stacks.math.columbia.edu/tag/XXXX |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://stylelint.io/)** | 404 | https://stylelint.io/%29%2A%2A |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://tc39.es/ecmascript-asyncawait/ | 404 | https://tc39.es/ecmascript-asyncawait/ |
| `数学家理念体系/阿蒂亚数学理念/START-HERE.md` | https://www.abelprize.no/laureates/2004 | 404 | https://abelprize.no/laureates/2004 |
| `docs/07-数理逻辑/INDEX.md` | https://www.cs.cmu.edu/~fp/courses/15317-f18/ | 404 | https://www.cs.cmu.edu/~fp/courses/15317-f18/ |
| `docs/01-基础数学/国际标准对照索引.md` | https://www.ens.fr/departements/mathematiques | 404 | https://www.ens.psl.eu/departements/mathematiques |
| `docs/generated/i18n/en/国际标准对照索引.md` | https://www.ens.fr/departements/mathematiques | 404 | https://www.ens.psl.eu/departements/mathematiques |
| `docs/generated/i18n/zh/国际标准对照索引.md` | https://www.ens.fr/departements/mathematiques | 404 | https://www.ens.psl.eu/departements/mathematiques |
| `docs/01-基础数学/自然数构造-国际标准对照版.md` | https://www.ens.fr/enseignement/cours/logique-et-theorie-des-ensembles | 404 | https://www.ens.psl.eu/enseignement/cours/logique-et-theorie-des-ensembles |
| `docs/generated/i18n/en/自然数构造-国际标准对照版.md` | https://www.ens.fr/enseignement/cours/logique-et-theorie-des-ensembles | 404 | https://www.ens.psl.eu/enseignement/cours/logique-et-theorie-des-ensembles |
| `docs/generated/i18n/zh/自然数构造-国际标准对照版.md` | https://www.ens.fr/enseignement/cours/logique-et-theorie-des-ensembles | 404 | https://www.ens.psl.eu/enseignement/cours/logique-et-theorie-des-ensembles |
| `数学家理念体系/德利涅数学理念/02-数学内容深度分析/01-Weil猜想与证明.md` | https://www.ihes.fr/deligne/ | 404 | https://www.ihes.fr/deligne/ |
| `docs/21-最优化/01-线性规划-工业级深化版.md` | https://www.kaggle.com/datasets/supply-chain | 404 | https://www.kaggle.com/datasets/supply-chain |
| `docs/09-形式化证明/00-从FormalMath到Mathlib4学习路径.md` | https://www.leanprover.cn/math-in-lean/ | 404 | https://www.leanprover.cn/math-in-lean/ |
| `数学家理念体系/00-ONLINE-RESOURCES-ALIGNMENT.md` | https://www.maa.org/press/maa-reviews/hilbert | 404 | https://maa.org/press/maa-reviews/hilbert |
| `docs/12-学术资源/03-Caltech数学课程对齐报告.md` | https://www.math.caltech.edu/courses | 404 | https://www.math.caltech.edu/courses |
| `project/00-权威源复核清单.md` | https://www.math.harvard.edu/course/mathematics-232br/；2025 | 404 | https://www.math.harvard.edu/course/mathematics-232br/%EF%BC%9B2025 |
| `docs/02-代数结构/07-项目文档/项目总览/抽象代数结构全面分析计划-2025年1月.md` | https://www.math.harvard.edu/undergraduate/course/abstract-algebra/ | 404 | https://www.math.harvard.edu/undergraduate/course/abstract-algebra/ |
| `project/Princeton-course-mapping.md` | https://www.math.princeton.edu/people/faculty | 404 | https://www.math.princeton.edu/people/faculty |
| `project/00-权威源年度复核报告-2026年4月.md` | https://www.math.princeton.edu/undergraduate/honors | 404 | https://www.math.princeton.edu/undergraduate/honors |
| `project/Princeton-course-mapping-detailed.md` | https://www.math.princeton.edu/undergraduate/honors | 404 | https://www.math.princeton.edu/undergraduate/honors |
| `project/00-权威源年度复核报告-2026年4月.md` | https://www.math.princeton.edu/undergraduate/independent-work | 404 | https://www.math.princeton.edu/undergraduate/independent-work |
| `project/00-权威源年度复核报告-2026年4月.md` | https://www.math.princeton.edu/undergraduate/junior-seminar | 404 | https://www.math.princeton.edu/undergraduate/junior-seminar |
| `project/Princeton-course-mapping-detailed.md` | https://www.math.princeton.edu/undergraduate/junior-seminar | 404 | https://www.math.princeton.edu/undergraduate/junior-seminar |
| `concept/00-权威资源对标改进计划.md` | https://www.math.princeton.edu/undergraduate/major-requirements | 404 | https://www.math.princeton.edu/undergraduate/major-requirements |
| `project/00-权威源年度复核报告-2026年4月.md` | https://www.math.princeton.edu/undergraduate/senior-thesis | 404 | https://www.math.princeton.edu/undergraduate/senior-thesis |
| `project/Princeton-course-mapping-detailed.md` | https://www.math.princeton.edu/undergraduate/senior-thesis | 404 | https://www.math.princeton.edu/undergraduate/senior-thesis |
| `docs/01-基础数学/自然数构造-国际标准对照版.md` | https://www.maths.cam.ac.uk/undergrad/course/ia/numbers-and-sets | 404 | https://www.maths.cam.ac.uk/undergrad/course/ia/numbers-and-sets |
| `docs/generated/i18n/en/自然数构造-国际标准对照版.md` | https://www.maths.cam.ac.uk/undergrad/course/ia/numbers-and-sets | 404 | https://www.maths.cam.ac.uk/undergrad/course/ia/numbers-and-sets |
| `docs/generated/i18n/zh/自然数构造-国际标准对照版.md` | https://www.maths.cam.ac.uk/undergrad/course/ia/numbers-and-sets | 404 | https://www.maths.cam.ac.uk/undergrad/course/ia/numbers-and-sets |
| `docs/01-基础数学/国际标准对照索引.md` | https://www.mathunion.org/icm/ | 404 | https://www.mathunion.org/icm/ |
| `docs/generated/i18n/en/国际标准对照索引.md` | https://www.mathunion.org/icm/ | 404 | https://www.mathunion.org/icm/ |
| `docs/generated/i18n/zh/国际标准对照索引.md` | https://www.mathunion.org/icm/ | 404 | https://www.mathunion.org/icm/ |
| `数学家理念体系/00-ONLINE-RESOURCES-ALIGNMENT.md` | https://www.springer.com/gp/book/9783642867668 | 404 | https://link.springer.com/book/9783642867668 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://www.theory.caltech.edu/~preskill/ph219 | 404 | https://www.theory.caltech.edu/~preskill/ph219 |
| `数学家理念体系/图灵数学理念/04-历史与传记/01-生平与学术历程.md` | https://www.turingarchive.org/ | 400 | https://www.turingarchive.org/ |
| `docs/01-基础数学/国际标准对照索引.md` | https://www.uni-goettingen.de/de/mathematik/ | 404 | https://www.uni-goettingen.de/de/mathematik/ |
| `docs/generated/i18n/en/国际标准对照索引.md` | https://www.uni-goettingen.de/de/mathematik/ | 404 | https://www.uni-goettingen.de/de/mathematik/ |
| `docs/generated/i18n/zh/国际标准对照索引.md` | https://www.uni-goettingen.de/de/mathematik/ | 404 | https://www.uni-goettingen.de/de/mathematik/ |
| `docs/01-基础数学/自然数构造-国际标准对照版.md` | https://www.uni-goettingen.de/de/veranstaltungen/ | 404 | https://www.uni-goettingen.de/de/veranstaltungen/ |
| `docs/generated/i18n/en/自然数构造-国际标准对照版.md` | https://www.uni-goettingen.de/de/veranstaltungen/ | 404 | https://www.uni-goettingen.de/de/veranstaltungen/ |
| `docs/generated/i18n/zh/自然数构造-国际标准对照版.md` | https://www.uni-goettingen.de/de/veranstaltungen/ | 404 | https://www.uni-goettingen.de/de/veranstaltungen/ |
| `docs/可视化内容/00-可视化总览.md` | https://www.wolframalpha.com | 404 | https://www.wolframalpha.com |
| `docs/12-学术资源/18-数学科普视频资源索引.md` | https://www.youtube.com/c/standupmaths | 404 | https://www.youtube.com/c/standupmaths |
| `docs/应用案例库/01-物理学应用/01-量子力学群论对称性.md` | https://www.youtube.com/playlist?example | 404 | https://www.youtube.com/playlist?example |

## 四、不确定/瞬态链接清单（前 200 条）

| 文档路径 | 原链接 | 状态码 | 最终 URL |
|----------|--------|--------|----------|
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://andrewhillcode.com | 500 | http://andrewhillcode.com |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/cli-width | 403 | https://www.npmjs.com/package/cli-width |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/dompurify | 403 | https://www.npmjs.com/package/dompurify |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/engine.io-client | 403 | https://www.npmjs.com/package/engine.io-client |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/escodegen | 403 | https://www.npmjs.com/package/escodegen |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/eventemitter2 | 403 | https://www.npmjs.com/package/eventemitter2 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/harmony-reflect | 403 | https://www.npmjs.com/package/harmony-reflect |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/react-fast-compare | 403 | https://www.npmjs.com/package/react-fast-compare |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/rxjs | 403 | https://www.npmjs.com/package/rxjs |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://badge.fury.io/js/socket.io-parser | 403 | https://www.npmjs.com/package/socket.io-parser |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://bioinformatics.oxfordjournals.org/content/32/2/309.full.pdf | 403 | http://bioinformatics.oxfordjournals.org/content/32/2/309.full.pdf |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://bithavoc.io | 500 | http://bithavoc.io |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://blog.alfrescian.com | 500 | http://leere.seite/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://bolinfest.com/essays/json.html | 403 | https://bolinfest.com/essays/json.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://calvinmetcalf.com/post/61672207151/setimmediate-etc | 403 | https://calvinmetcalf.com/post/61672207151/setimmediate-etc |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://calvinmetcalf.com/post/61761231881/javascript-schedulers | 403 | https://calvinmetcalf.com/post/61761231881/javascript-schedulers |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ci.testling.com/Raynos/xtend | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | http://ci.testling.com/Raynos/xtend |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ci.testling.com/Raynos/xtend.png | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | http://ci.testling.com/Raynos/xtend.png |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://cmap.ihmc.us/publications/ResearchPapers/ | 403 | https://cmap.ihmc.us/publications/ResearchPapers/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://cmc.ihmc.us | 500 | https://cmc.ihmc.us/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://codeflow.org/entries/2012/aug/05/webgl-rendering-of-solid-trails/ | 500 | http://codeflow.org/entries/2012/aug/05/webgl-rendering-of-solid-trails/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://conorhastings.com | 500 | http://conorhastings.com |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://custom-docs.com' | 500 | http://custom-docs.com' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://dejavis.org/linechart | 500 | http://dejavis.org/linechart |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://devtoolscommunity.herokuapp.com)_ | 500 | http://devtoolscommunity.herokuapp.com)_ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://divyanshu.xyz | 403 | https://stackoverflow.com/users/story/4952669 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://docs.libuv.org/en/v1.x/threadpool.html | 429 | http://docs.libuv.org/en/v1.x/threadpool.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://docs.libuv.org/en/v1.x/threadpool.html#thread-pool-work-scheduling | 429 | http://docs.libuv.org/en/v1.x/threadpool.html#thread-pool-work-scheduling |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://en.wikipedia.org/' | 403 | https://en.wikipedia.org/%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://en.wikipedia.org/wiki/URI_scheme)-dependent | 403 | https://en.wikipedia.org/wiki/URI_scheme%29-dependent |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://endpoint-server.com/some-url | 500 | http://endpoint-server.com/some-url |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com' | 500 | http://example.com' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://example.com* | 500 | http://example.com* |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://examplé.org/rosé | 500 | http://xn--exampl-gva.org/ros%C3%A9 |
| `docs/00-2025年arXiv数学前沿追踪-第1季度.md` | http://export.arxiv.org/api/ | 503 | https://export.arxiv.org/api/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://export.arxiv.org/api/ | 503 | https://export.arxiv.org/api/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://export.arxiv.org/api/query | The read operation timed out | http://export.arxiv.org/api/query |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://foo.bar/dummy.json' | 500 | http://foo.bar/dummy.json%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://highlightjs.readthedocs.io/ | 502 | https://highlightjs.readthedocs.io/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://hudson-ci.org | 500 | http://hudson-ci.org |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ie.microsoft.com/testdrive/Performance/setImmediateSorting/Default.html | 500 | http://ie.microsoft.com/testdrive/Performance/setImmediateSorting/Default.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://images.google.com' | 500 | http://images.google.com' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://jonathanstoye.de | 500 | http://jonathan-stoye-linkedin.s3-website.eu-central-1.amazonaws.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://jsbin.com/fiqugiq | 403 | http://jsbin.com/fiqugiq |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://julien.isonoe.net | [SSL: TLSV1_ALERT_INTERNAL_ERROR] tlsv1 alert internal error (_ssl.c:1032) | http://julien.isonoe.net |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://katieboedges.com/ | 500 | http://katieboedges.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://kengregory.com | 403 | https://kengregory.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://leere.seite/ | 500 | http://leere.seite/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://lichess.org/@/StevenEmily | 429 | https://lichess.org/%40/StevenEmily |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://linux.die.net/man/2/connect | 403 | https://linux.die.net/man/2/connect |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://localproxy.com' | 500 | http://localproxy.com' |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://makeapullrequest.com | 403 | https://makeapullrequest.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mikeal.iriscouch.com/testjs/' | 500 | http://mikeal.iriscouch.com/testjs/%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mikeal.iriscouch.com/testjs/'+ | 500 | http://mikeal.iriscouch.com/testjs/%27%2B |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mizar.org/ | 500 | http://mizar.org/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mkweb.bcgsc.ca/circos/guide/tables/ | 403 | https://mkweb.bcgsc.ca/circos/guide/tables/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://mxr.mozilla.org/mozilla-central/source/netwerk/test/unit/data/test_psl.txt?raw=1 | 500 | http://mxr.mozilla.org/mozilla-central/source/netwerk/test/unit/data/test_psl.txt?raw=1 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://nodeca.github.com/argparse/ | 500 | http://nodeca.github.com/argparse/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://nodeca.github.com/js-yaml/ | 500 | http://nodeca.github.com/js-yaml/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://nodeca.github.com/js-yaml/)__ | 500 | http://nodeca.github.com/js-yaml/%29__ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/@isaacs/ttlcache | 403 | https://www.npmjs.com/%40isaacs/ttlcache |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/@nodelib/fs.walk | 403 | https://www.npmjs.com/%40nodelib/fs.walk |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/cacache | 403 | https://www.npmjs.com/cacache |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/cliui | 403 | https://www.npmjs.com/cliui |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/fast-glob | 403 | https://www.npmjs.com/fast-glob |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/fast-glob)_ | 403 | https://www.npmjs.com/fast-glob%29_ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/fastparallel | 403 | https://www.npmjs.com/fastparallel |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/fastseries | 403 | https://www.npmjs.com/fastseries |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/fs-minipass | 403 | https://www.npmjs.com/fs-minipass |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/glob | 403 | https://www.npmjs.com/glob |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/globby | 403 | https://www.npmjs.com/globby |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/globby)_ | 403 | https://www.npmjs.com/globby%29_ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/graceful-fs | 403 | https://www.npmjs.com/graceful-fs |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/lru-cache | 403 | https://www.npmjs.com/lru-cache |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/make-fetch-happen | 403 | https://www.npmjs.com/make-fetch-happen |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/minipass | 403 | https://www.npmjs.com/minipass |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/minipass-collect | 403 | https://www.npmjs.com/minipass-collect |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/minipass-fetch | 403 | https://www.npmjs.com/minipass-fetch |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/minipass-flush | 403 | https://www.npmjs.com/minipass-flush |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/minipass-json-stream | 403 | https://www.npmjs.com/minipass-json-stream |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/minipass-pipeline | 403 | https://www.npmjs.com/minipass-pipeline |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/minipass-sized | 403 | https://www.npmjs.com/minipass-sized |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/minizlib | 403 | https://www.npmjs.com/minizlib |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/npm-registry-fetch | 403 | https://www.npmjs.com/npm-registry-fetch |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/once | 403 | https://www.npmjs.com/once |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/pacote | 403 | https://www.npmjs.com/pacote |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/path-scurry | 403 | https://www.npmjs.com/path-scurry |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/ssri | 403 | https://www.npmjs.com/ssri |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/tap | The read operation timed out | http://npm.im/tap |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/tap-parser | 403 | https://www.npmjs.com/tap-parser |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/tar | 403 | https://www.npmjs.com/tar |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/treport | 403 | https://www.npmjs.com/treport |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npm.im/yargs | 403 | https://www.npmjs.com/yargs |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npmjs.com/package/dedent | 403 | https://www.npmjs.com/package/dedent |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npmjs.com/package/ts-api-utils | 429 | https://npmjs.com/package/ts-api-utils |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npmjs.org | 403 | https://www.npmjs.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npmjs.org/ | 403 | https://www.npmjs.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npmjs.org/package/common-tags | 403 | https://www.npmjs.com/package/common-tags |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npmjs.org/package/glob | 403 | https://www.npmjs.com/package/glob |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://npmjs.org/yauzl | 403 | https://www.npmjs.com/yauzl |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://nuances.co | 500 | http://nuances.co |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://oai.cwi.nl/oai/asset/21856/21856B.pdf | 500 | http://oai.cwi.nl/oai/asset/21856/21856B.pdf |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://ociweb.com/mark/ | 500 | http://ociweb.com/mark/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://orgs.man.ac.uk/projects/include/experiment/communities.htm | 500 | http://orgs.man.ac.uk/projects/include/experiment/communities.htm |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://peterolson.github.com/BigInteger.js/BigInteger.min.js | 500 | http://peterolson.github.com/BigInteger.js/BigInteger.min.js |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm | 500 | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://preludels.com)** | 500 | http://preludels.com)** |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://promises-aplus.github.com/promises-spec | 500 | http://promises-aplus.github.com/promises-spec |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://promises-aplus.github.com/promises-spec/ | 500 | http://promises-aplus.github.com/promises-spec/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://promises-aplus.github.com/promises-spec/assets/logo-small.png | 500 | http://promises-aplus.github.com/promises-spec/assets/logo-small.png |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://rbrtsmith.com/ | 500 | http://rbrtsmith.com/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://sivkoff.com | 500 | http://sivkoff.com |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://slack.socket.io | 500 | http://slack.socket.io |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://slack.socket.io/badge.svg | 500 | http://slack.socket.io/badge.svg |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://some-other-site.com/img.jpg' | 500 | http://some-other-site.com/img.jpg%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://some.server.com/' | 500 | http://some.server.com/%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://some.server.com/').auth('username' | 500 | http://some.server.com/%27%29.auth%28%27username%27 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://some.server.com/').auth(null | 500 | http://some.server.com/%27%29.auth%28null |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://stackoverflow.com/questions/13227489 | 403 | https://stackoverflow.com/questions/13227489 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://stackoverflow.com/questions/183485/can-anyone-recommend-a-good-free-javascript-for-punycode-to-unicode-conversion/301287#301287 | 403 | https://stackoverflow.com/questions/183485/can-anyone-recommend-a-good-free-javascript-for-punycode-to-unicode-conversion/301287#301287 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://stackoverflow.com/questions/tagged/bluebird | 403 | https://stackoverflow.com/questions/tagged/bluebird |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://stackoverflow.com/questions/tagged/typescript | 403 | https://stackoverflow.com/questions/tagged/typescript |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://standards.nctm.org/document/chapter3/index.htm | 500 | http://standards.nctm.org/document/chapter3/index.htm |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://superuser.com/a/176395/6877 | 403 | https://superuser.com/a/176395/6877 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://superuser.com/questions/104845/permission-to-make-symbolic-links-in-windows-7 | 403 | https://superuser.com/questions/104845/permission-to-make-symbolic-links-in-windows-7 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://terrencewwong.com | 500 | http://terrencewwong.com |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://tj.github.com/commander.js/ | 500 | http://tj.github.com/commander.js/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/#!/search/realtime/%23typescript | 520 | http://twitter.com/#%21%2Fsearch%2Frealtime%2F%23typescript |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/Constellation | 520 | http://twitter.com/Constellation |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/alex4Zero | 520 | http://twitter.com/alex4Zero |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/ariyahidayat | 520 | http://twitter.com/ariyahidayat |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/benjamincoe | 520 | http://twitter.com/benjamincoe |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/dan_abramov | 520 | http://twitter.com/dan_abramov |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/eush77 | 520 | http://twitter.com/eush77 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/jonschlinkert | 520 | http://twitter.com/jonschlinkert |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/mindmelting | 520 | http://twitter.com/mindmelting |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/rvagg | 520 | http://twitter.com/rvagg |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/winfinit | 520 | http://twitter.com/winfinit |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | http://twitter.com/zeke | 520 | http://twitter.com/zeke |
| `数学家理念体系/德利涅数学理念/02-数学内容深度分析/03-motives与Grothendieck纲领.md` | http://www.grothendieck-circle.org/ | 500 | http://www.grothendieck-circle.org/ |
| `docs/11-高级数学/symplectic-mirror.md` | http://www.stringwiki.org/ | The read operation timed out | http://www.stringwiki.org/ |
| `docs/01-基础数学/形式化验证标准-国际标准版.md` | https://agda.readthedocs.io/ | The read operation timed out | https://agda.readthedocs.io/ |
| `docs/07-数理逻辑/INDEX.md` | https://agda.readthedocs.io/ | The read operation timed out | https://agda.readthedocs.io/ |
| `docs/generated/i18n/en/形式化验证标准-国际标准版.md` | https://agda.readthedocs.io/ | 502 | https://agda.readthedocs.io/ |
| `docs/generated/i18n/zh/形式化验证标准-国际标准版.md` | https://agda.readthedocs.io/ | The read operation timed out | https://agda.readthedocs.io/ |
| `docs/开发文档/03-前端开发指南.md` | https://api.formalmath.org/api/v1 | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.formalmath.org/api/v1 |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://bolinfest.com/essays/json.html | 403 | https://bolinfest.com/essays/json.html |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://calvinmetcalf.com/post/61672207151/setimmediate-etc | 403 | https://calvinmetcalf.com/post/61672207151/setimmediate-etc |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://calvinmetcalf.com/post/61761231881/javascript-schedulers | 403 | https://calvinmetcalf.com/post/61761231881/javascript-schedulers |
| `docs/管理员手册/02-部署指南.md` | https://cdn.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://cdn.formalmath.org |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://cmap.ihmc.us/publications/ResearchPapers/ | 403 | https://cmap.ihmc.us/publications/ResearchPapers/ |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://cmc.ihmc.us/ | 500 | https://cmc.ihmc.us/ |
| `数学家理念体系/00-ONLINE-RESOURCES-ALIGNMENT.md` | https://dl.acm.org/ | 403 | https://dl.acm.org/ |
| `docs/00-认知诊断系统使用指南.md` | https://docs.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://docs.formalmath.org |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1002/hbm.460020402 | 403 | https://onlinelibrary.wiley.com/doi/10.1002/hbm.460020402 |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1080/02643290244000239 | 403 | https://www.tandfonline.com/doi/abs/10.1080/02643290244000239 |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1093/oxfordhb/9780199642342.013.041 | 403 | https://academic.oup.com/edited-volume/34494/chapter/292679312 |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1207/s15516709cog0502_2 | 403 | https://onlinelibrary.wiley.com/doi/10.1207/s15516709cog0502_2 |
| `concept/view/07-国际数学教育研究/03-新加坡数学教育/03-新加坡数学教育.md` | https://doi.org/10.5951/jresematheduc.40.3.0282 | 403 | https://pubs.nctm.org/view/journals/jrme/40/3/article-p282.xml |
| `project/00-项目进度报告/Phase1-全库外部链接校验报告.md` | https://en.wikipedia.org/' | 403 | https://en.wikipedia.org/%27 |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/01-可计算性哲学.md` | https://en.wikipedia.org/wiki/Alan_Turing)** | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/Alan_Turing)** |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/04-图灵机理论.md` | https://en.wikipedia.org/wiki/Alan_Turing)** | 403 | https://en.wikipedia.org/wiki/Alan_Turing%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/05-人工智能哲学.md` | https://en.wikipedia.org/wiki/Alan_Turing)** | 403 | https://en.wikipedia.org/wiki/Alan_Turing%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/04-与格洛腾迪克的合作理念.md` | https://en.wikipedia.org/wiki/Alexander_Grothendieck)** | 403 | https://en.wikipedia.org/wiki/Alexander_Grothendieck%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/鲁里数学理念/01-核心理论/04-与格洛腾迪克的传承.md` | https://en.wikipedia.org/wiki/Alexander_Grothendieck)** | 403 | https://en.wikipedia.org/wiki/Alexander_Grothendieck%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/01-数学哲学与方法论.md` | https://en.wikipedia.org/wiki/Algebraic_geometry)** | 403 | https://en.wikipedia.org/wiki/Algebraic_geometry%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/02-层论纲领.md` | https://en.wikipedia.org/wiki/Algebraic_geometry)** | 403 | https://en.wikipedia.org/wiki/Algebraic_geometry%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/03-代数几何现代化思想.md` | https://en.wikipedia.org/wiki/Algebraic_geometry)** | 403 | https://en.wikipedia.org/wiki/Algebraic_geometry%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/04-与格洛腾迪克的合作理念.md` | https://en.wikipedia.org/wiki/Algebraic_geometry)** | 403 | https://en.wikipedia.org/wiki/Algebraic_geometry%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/05-数学写作与教育理念.md` | https://en.wikipedia.org/wiki/Algebraic_geometry)** | 403 | https://en.wikipedia.org/wiki/Algebraic_geometry%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/01-数学哲学与方法论.md` | https://en.wikipedia.org/wiki/Algebraic_geometry_and_analytic_geometry)** | 403 | https://en.wikipedia.org/wiki/Algebraic_geometry_and_analytic_geometry%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/02-算法理论思想.md` | https://en.wikipedia.org/wiki/Algorithm)** | 403 | https://en.wikipedia.org/wiki/Algorithm%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/02-算法理论思想.md` | https://en.wikipedia.org/wiki/Algorithm_design)** | 403 | https://en.wikipedia.org/wiki/Algorithm_design%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/05-人工智能哲学.md` | https://en.wikipedia.org/wiki/Artificial_intelligence)** | 403 | https://en.wikipedia.org/wiki/Artificial_intelligence%29%2A%2A |
| `数学家理念体系/魏尔斯特拉斯数学理念/01-核心理论/05-数学写作与教育理念.md` | https://en.wikipedia.org/wiki/Berlin_School_of_Mathematics | 403 | https://en.wikipedia.org/wiki/Berlin_School_of_Mathematics |
| `数学家理念体系/00-归档-2026年4月-其他数学家/布劳威尔数学理念/01-核心理论/01-直觉主义哲学基础.md` | https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation)** | 403 | https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/布劳威尔数学理念/01-核心理论/02-构造性数学纲领.md` | https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation)** | 403 | https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/布劳威尔数学理念/01-核心理论/05-直觉主义逻辑的形式化.md` | https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation)** | 403 | https://en.wikipedia.org/wiki/Brouwer%E2%80%93Heyting%E2%80%93Kolmogorov_interpretation%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/布劳威尔数学理念/01-核心理论/03-排中律批判与自由选择序列.md` | https://en.wikipedia.org/wiki/Brouwer%E2%80%93Hilbert_controversy)** | 403 | https://en.wikipedia.org/wiki/Brouwer%E2%80%93Hilbert_controversy%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/康托尔数学理念/01-核心理论/01-集合论哲学基础.md` | https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)** | 403 | https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/康托尔数学理念/01-核心理论/02-无穷概念的数学化.md` | https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)** | 403 | https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/康托尔数学理念/01-核心理论/03-对角线方法与证明技术.md` | https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)** | 403 | https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/康托尔数学理念/01-核心理论/04-基数与序数理论.md` | https://en.wikipedia.org/wiki/Cantor%27s_theorem)** | 403 | https://en.wikipedia.org/wiki/Cantor%27s_theorem%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/康托尔数学理念/01-核心理论/01-集合论哲学基础.md` | https://en.wikipedia.org/wiki/Cardinal_number)** | 403 | https://en.wikipedia.org/wiki/Cardinal_number%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/康托尔数学理念/01-核心理论/02-无穷概念的数学化.md` | https://en.wikipedia.org/wiki/Cardinal_number)** | 403 | https://en.wikipedia.org/wiki/Cardinal_number%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/康托尔数学理念/01-核心理论/04-基数与序数理论.md` | https://en.wikipedia.org/wiki/Cardinal_number)** | 403 | https://en.wikipedia.org/wiki/Cardinal_number%29%2A%2A |
| `数学家理念体系/雅可比数学理念/01-核心理论/05-学术影响与传承.md` | https://en.wikipedia.org/wiki/Carl_Gustav_Jacob_Jacobi | The read operation timed out | https://en.wikipedia.org/wiki/Carl_Gustav_Jacob_Jacobi |
| `concept/00-范畴论视角-核心概念分析/26-素数-范畴论视角分析.md` | https://en.wikipedia.org/wiki/Category_(mathematics) | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/Category_(mathematics) |
| `concept/00-范畴论视角-核心概念分析/29-图-范畴论视角分析.md` | https://en.wikipedia.org/wiki/Category_of_graphs | 403 | https://en.wikipedia.org/wiki/Category_of_graphs |
| `数学家理念体系/00-归档-2026年4月-其他数学家/鲁里数学理念/01-核心理论/04-与格洛腾迪克的传承.md` | https://en.wikipedia.org/wiki/Category_theory)** | 403 | https://en.wikipedia.org/wiki/Category_theory%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/鲁里数学理念/01-核心理论/05-数学写作与教育理念.md` | https://en.wikipedia.org/wiki/Category_theory)** | 403 | https://en.wikipedia.org/wiki/Category_theory%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/05-人工智能哲学.md` | https://en.wikipedia.org/wiki/Chinese_room)** | 403 | https://en.wikipedia.org/wiki/Chinese_room%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/01-可计算性哲学.md` | https://en.wikipedia.org/wiki/Church%E2%80%93Turing_thesis)** | 403 | https://en.wikipedia.org/wiki/Church%E2%80%93Turing_thesis%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/04-图灵机理论.md` | https://en.wikipedia.org/wiki/Church%E2%80%93Turing_thesis)** | 403 | https://en.wikipedia.org/wiki/Church%E2%80%93Turing_thesis%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/01-数学哲学与方法论.md` | https://en.wikipedia.org/wiki/Cohomology)** | 403 | https://en.wikipedia.org/wiki/Cohomology%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/02-层论纲领.md` | https://en.wikipedia.org/wiki/Cohomology)** | 403 | https://en.wikipedia.org/wiki/Cohomology%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/塞尔数学理念/01-核心理论/03-代数几何现代化思想.md` | https://en.wikipedia.org/wiki/Cohomology)** | 403 | https://en.wikipedia.org/wiki/Cohomology%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/01-可计算性哲学.md` | https://en.wikipedia.org/wiki/Computability_theory)** | 403 | https://en.wikipedia.org/wiki/Computability_theory%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/布劳威尔数学理念/01-核心理论/04-数学对象的构造性理论.md` | https://en.wikipedia.org/wiki/Computable_number)** | 403 | https://en.wikipedia.org/wiki/Computable_number%29%2A%2A |
| `数学家理念体系/00-归档-2026年4月-其他数学家/图灵数学理念/01-核心理论/02-算法理论思想.md` | https://en.wikipedia.org/wiki/Computational_complexity_theory)** | 403 | https://en.wikipedia.org/wiki/Computational_complexity_theory%29%2A%2A |

## 五、说明

- **确认失效**：`404`、不可解析主机、非瞬态 `4xx` 等，需要替换或删除。
- **不确定/瞬态**：`403/429` 频率限制、`5xx`、超时、SSL 握手异常等，建议人工复核或稍后重试。
- `301/302` 跳转后的目标若返回 `200`，视为可用。
- Wikidata 实体页因对批量 HEAD 敏感，已跳过校验。