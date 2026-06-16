---
title: Phase 1 全库外部链接校验报告
level: meta
processed_at: '2026-06-16T17:50:20.432420'
review_status: draft
---

# Phase 1 全库外部链接校验报告

**校验时间**: 2026年06月16日 17:50
**校验范围**: 全库 Markdown 文档（排除 node_modules / .git / dist / build / 00-归档 等）
**检查链接总数**: 27316
**确认失效链接数**: 78 | **不确定/瞬态链接数**: 2139
**涉及唯一 URL 数**: 3239

## 一、按文档分类统计

| 分类 | 检查链接数 | 确认失效 | 不确定/瞬态 |
|------|-----------|---------|------------|
| docs | 12684 | 37 | 267 |
| mathematicians | 10331 | 0 | 1462 |
| other | 1925 | 20 | 179 |
| FormalMath-Enhanced | 1060 | 7 | 128 |
| concept | 799 | 0 | 80 |
| project | 489 | 12 | 14 |
| FormalMath-Interactive | 28 | 2 | 9 |

## 二、确认失效链接按域名汇总（Top 30）

| 域名 | 失效数 |
|------|-------|
| people.math.harvard.edu | 45 |
|  | 6 |
| www.d.umn.edu | 4 |
| www.merga.net.au | 2 |
| www.aare.edu.au | 2 |
| www.swinburne.edu.au | 2 |
| web.stanford.edu | 1 |
| www.s.u-tokyo.ac.jp | 1 |
| 10 | 1 |
| api.github.com | 1 |
| $server_name$request_uri | 1 |
| msc2020.org | 1 |
| redis.io | 1 |
| openwebmath.github.io | 1 |
| github.com | 1 |
| twitter.com | 1 |
| www.ethz.ch | 1 |
| people.maths.ox.ac.uk | 1 |
| www.routledge.com | 1 |
| dl.google.com | 1 |
| www.jmilne.org | 1 |
| stacks.math.columbia.edu | 1 |
| www.pz.harvard.edu | 1 |

## 三、确认失效链接清单（前 500 条）

| 文档路径 | 原链接 | 状态码 | 最终 URL |
|----------|--------|--------|----------|
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | http:// | no host given | http:// |
| `00-外部链接修复报告.md` | http://10 | [Errno 11001] getaddrinfo failed | http://10 |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.aare.edu.au/06pap/afa06011.pdf | 404 | https://www.aare.edu.au/06pap/afa06011.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.aare.edu.au/06pap/afa06011.pdf | 404 | https://www.aare.edu.au/06pap/afa06011.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.merga.net.au/documents/RP12007.pdf | 404 | http://www.merga.net.au/documents/RP12007.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.merga.net.au/documents/RP12007.pdf | 404 | http://www.merga.net.au/documents/RP12007.pdf |
| `research/06-思维表征/表征方式/03-矩阵对比.md` | http://www.pz.harvard.edu/thinking-routines | 404 | http://www.pz.harvard.edu/thinking-routines |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.swinburne.edu.au/lss/statistics/IASE/CD | 404 | https://www.swinburne.edu.au/lss/statistics/IASE/CD |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.swinburne.edu.au/lss/statistics/IASE/CD | 404 | https://www.swinburne.edu.au/lss/statistics/IASE/CD |
| `00-外部链接修复报告.md` | https:// | no host given | https:// |
| `FormalMath-Enhanced/api/NOTIFICATION_SYSTEM_SUMMARY.md` | https:// | no host given | https:// |
| `FormalMath-Enhanced/api/app/notifications/README.md` | https:// | no host given | https:// |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https:// | no host given | https:// |
| `docs/链接维护指南.md` | https:// | no host given | https:// |
| `docs/管理员手册/05-安全管理.md` | https://$server_name$request_uri | [Errno 11001] getaddrinfo failed | https://$server_name$request_uri |
| `.github/CI_CD_GUIDE.md` | https://api.github.com/repos/formalmath/formalmath/actions/workflows/test.yml/dispatches | 404 | https://api.github.com/repos/formalmath/formalmath/actions/workflows/test.yml/dispatches |
| `ref/Books/AbstractAlgebra/Paulsen W. Abstract Algebra. An Interactive Approach 3ed 2025/full.md` | https://dl.google.com/linux/direct/google-chrome-stable_current_amd64deb | 404 | https://dl.google.com/linux/direct/google-chrome-stable_current_amd64deb |
| `FormalMath-Interactive/DEPLOY.md` | https://github.com/FormalMath/wiki | 404 | https://github.com/FormalMath/wiki |
| `FormalMath-Enhanced/01-MSC-Coding/00-MSC2020-编码标准说明.md` | https://msc2020.org/resources/MSC/2020/MSC2020.rdf | 404 | https://msc2020.org/resources/MSC/2020/MSC2020.rdf |
| `FormalMath-Enhanced/05-AI-Formalization/02-DeepSeek-Math.md` | https://openwebmath.github.io/ | 404 | https://openwebmath.github.io/ |
| `docs/00-知识层次体系/L1-形式化定义层/05-拓扑学基础/01-拓扑空间.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.1-层的基本性质.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.2-概形的基本性质.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.3-态射性质.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.4-分离性与本征性.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.5-模与层-续.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.5-模与层.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.6-除子.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.7-射影态射.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.8-微分形式.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/II.9-形式概形.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/III.2-导出函子与上同调基本性质.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/III.3-Čech上同调与导出上同调.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/III.4-上同调计算与应用.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/IV.1-IV.4-曲线基本理论.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/IV.5-IV.6-曲线深化.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/00-银层核心课程/Harvard-232br-代数几何/V.1-V.3-曲面初步.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.1-层的基本性质.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.2-概形的基本性质.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.3-态射性质.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.4-分离性与本征性.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.5-模与层-续.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.5-模与层.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.6-除子.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.7-射影态射.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.8-微分形式.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/II.9-形式概形.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/III.2-导出函子与上同调基本性质.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/III.3-Čech上同调与导出上同调.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/III.4-上同调计算与应用.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/IV.1-IV.4-曲线基本理论-习题解答.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/IV.5-IV.6-曲线深化.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/Harvard-232br-习题解答/V.1-V.3-曲面初步-习题解答.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/定理证明/Riemann-Roch定理-曲线-完整证明.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `docs/13-代数几何/定理证明/Serre消失定理-完整证明.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/Agent指令-Harvard-232br-Ch3-5.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/Harvard-232br-L3-定义对齐表.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/Harvard-232br-L4-定理对齐表.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/Harvard-232br-L5-习题对齐表.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/Harvard-232br-L6-思想方法提炼.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/Harvard-232br-习题系统建设计划.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/Harvard-232br-讲义逐章拆解索引.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/Harvard-Math232br-语义级对齐手册.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/v2-quality-rewrite/deliverables/D019-harvard-232br-definition-alignment.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/v2-quality-rewrite/workspaces/courses/harvard-232br/T009-syllabus-deconstruction/task-report.md` | https://people.math.harvard.edu/~phorne/232Br.html | 404 | https://people.math.harvard.edu/~phorne/232Br.html |
| `project/v2-quality-rewrite/workspaces/courses/harvard-232br/T009-syllabus-deconstruction/task-report.md` | https://people.maths.ox.ac.uk/liu/notes/s17-algebraic-geometry.pdf | 404 | https://people.maths.ox.ac.uk/liu/notes/s17-algebraic-geometry.pdf |
| `FormalMath-Enhanced/DEPLOYMENT.md` | https://redis.io/docs/manual/persistence/ | 404 | https://redis.io/docs/latest/manual/persistence/ |
| `ref/Stacks-Tag-解读/Tag-0A9L-导出Hilbert概形.md` | https://stacks.math.columbia.edu/chapter/0D4C | 404 | https://stacks.math.columbia.edu/chapter/0D4C |
| `FormalMath-Interactive/docs/SEO-Implementation-Report.md` | https://twitter.com/formalmath | 404 | https://x.com/formalmath |
| `00-Stanford课程内容对齐报告.md` | https://web.stanford.edu/~jluk/math61CMautumn19/ | 404 | https://web.stanford.edu/~jluk/math61CMautumn19/ |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://www.d.umn.edu/\~jgallian/JavafixB.html | 404 | https://www.d.umn.edu/%5C~jgallian/JavafixB.html |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://www.d.umn.edu/\~jgallian/msproject06/project_xukai7 | 404 | https://www.d.umn.edu/%5C~jgallian/msproject06/project_xukai7 |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://www.d.umn.edu/\~jgallian/msproject06/project_xukai7.html | 404 | https://www.d.umn.edu/%5C~jgallian/msproject06/project_xukai7.html |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://www.d.umn.edu/~jgallian/JavafixB.htmlm | 404 | https://www.d.umn.edu/~jgallian/JavafixB.htmlm |
| `project/ETH-Zurich-course-mapping.md` | https://www.ethz.ch/content/dam/ethz/special-interest/mavt/department-averoes/documents/Studium/Bachelor/Studienplan_BSc_MAVT_2023.pdf | 404 | https://ethz.ch/content/dam/ethz/special-interest/mavt/department-averoes/documents/Studium/Bachelor/Studienplan_BSc_MAVT_2023.pdf |
| `ref/Stacks-Tag-解读/Tag-03Q5-Etale上同调与正向极限交换.md` | https://www.jmilne.org/math/Books/EC.pdf | 404 | https://www.jmilne.org/math/Books/EC.pdf |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Student Solutions Manual for Gallian's Cont. Abstr. Algebra 11ed 2025/full.md` | https://www.routledge.com/Textbooks-in-Mathematics/book-series/ | 404 | https://www.routledge.com/Textbooks-in-Mathematics/book-series/ |
| `00-东京大学数学课程对齐报告.md` | https://www.s.u-tokyo.ac.jp/ja/admission/undergraduate/pdf/ms2022.pdf | 404 | https://www.s.u-tokyo.ac.jp/ja/admission/undergraduate/pdf/ms2022.pdf |

## 四、不确定/瞬态链接清单（前 200 条）

| 文档路径 | 原链接 | 状态码 | 最终 URL |
|----------|--------|--------|----------|
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://cmap.ihmc.us/publications/ResearchPapers/ | 403 | https://cmap.ihmc.us/publications/ResearchPapers/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://cmap.ihmc.us/publications/ResearchPapers/ | 403 | https://cmap.ihmc.us/publications/ResearchPapers/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://cmap.ihmc.us/publications/ResearchPapers/TheoryUnderlyingConceptMaps.pdf | timed out | http://cmap.ihmc.us/publications/ResearchPapers/TheoryUnderlyingConceptMaps.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://cmc.ihmc.us | 500 | https://cmc.ihmc.us/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://cmc.ihmc.us | 500 | https://cmc.ihmc.us/ |
| `ref/Books/AbstractAlgebra/Paulsen W. Abstract Algebra. An Interactive Approach 3ed 2025/full.md` | http://en.wikipedia.org | 403 | https://en.wikipedia.org/ |
| `00-外部链接修复报告.md` | http://export.arxiv.org/api/ | 429 | https://export.arxiv.org/api/ |
| `docs/00-2025年arXiv数学前沿追踪-第1季度.md` | http://export.arxiv.org/api/ | The read operation timed out | http://export.arxiv.org/api/ |
| `00-全局导航与快速参考.md` | http://mizar.org/ | 500 | http://mizar.org/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://orgs.man.ac.uk/projects/include/experiment/communities.htm | 500 | http://orgs.man.ac.uk/projects/include/experiment/communities.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://orgs.man.ac.uk/projects/include/experiment/communities.htm | 500 | http://orgs.man.ac.uk/projects/include/experiment/communities.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm | 500 | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm | 500 | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://standards.nctm.org/document/chapter3/index.htm | 500 | http://standards.nctm.org/document/chapter3/index.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://standards.nctm.org/document/chapter3/index.htm | 500 | http://standards.nctm.org/document/chapter3/index.htm |
| `concept/00-权威资源对标改进计划.md` | http://us.metamath.org/ | The read operation timed out | http://us.metamath.org/ |
| `concept/核心概念/01-集合.md` | http://us.metamath.org/mpeuni/mmset.html | The read operation timed out | http://us.metamath.org/mpeuni/mmset.html |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.aamt.edu.au/standards | 403 | https://www.aamt.edu.au/standards |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.aamt.edu.au/standards | 403 | https://www.aamt.edu.au/standards |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.aamt.edu.au/standards/standxtm.pdf | 403 | https://www.aamt.edu.au/standards/standxtm.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.aamt.edu.au/standards/standxtm.pdf | 403 | https://www.aamt.edu.au/standards/standxtm.pdf |
| `ref/Books/AbstractAlgebra/Alcock L. How to Think About Abstract Algebra 2021/full.md` | http://www.ams.org/ | 403 | http://www.ams.org/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.emis.de/proceedings/PME29/PME29RRPapers/PME29Vol3Hansson.pdf | 403 | https://zbmath.org/emis/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.emis.de/proceedings/PME29/PME29RRPapers/PME29Vol3Hansson.pdf | 403 | https://zbmath.org/emis/ |
| `数学家理念体系/德利涅数学理念/02-数学内容深度分析/03-motives与Grothendieck纲领.md` | http://www.grothendieck-circle.org/ | 500 | http://www.grothendieck-circle.org/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.unix.oit.umass.edu/~afeldman/ActionResearchPapers/Feldman1996.PDF | 500 | http://www.unix.oit.umass.edu/~afeldman/ActionResearchPapers/Feldman1996.PDF |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.unix.oit.umass.edu/~afeldman/ActionResearchPapers/Feldman1996.PDF | 500 | http://www.unix.oit.umass.edu/~afeldman/ActionResearchPapers/Feldman1996.PDF |
| `FormalMath-Enhanced/QUICKSTART.md` | http://your-domain.com:3000 | 500 | http://your-domain.com:3000 |
| `FormalMath-Enhanced/QUICKSTART.md` | http://your-domain.com:9090 | 500 | http://your-domain.com:9090 |
| `deploy/PRODUCTION_CHECKLIST.md` | https://alerts.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://alerts.formalmath.org |
| `tests/performance/README.md` | https://api-staging.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api-staging.formalmath.org |
| `FormalMath-Enhanced/deployment/cdn/QUICKSTART.md` | https://api.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api.formalmath.org |
| `tests/performance/README.md` | https://api.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api.formalmath.org |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https://api.formalmath.org/api/v1 | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api.formalmath.org/api/v1 |
| `docs/开发文档/03-前端开发指南.md` | https://api.formalmath.org/api/v1 | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api.formalmath.org/api/v1 |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https://api.formalmath.org/api/v1/concepts | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api.formalmath.org/api/v1/concepts |
| `FormalMath-Enhanced/deployment/cdn/QUICKSTART.md` | https://api.formalmath.org/api/v1/concepts | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api.formalmath.org/api/v1/concepts |
| `FormalMath-Enhanced/deployment/cdn/README.md` | https://api.formalmath.org/api/v1/concepts | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api.formalmath.org/api/v1/concepts |
| `00-上线检查清单与应急方案.md` | https://api.formalmath.org/health | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://api.formalmath.org/health |
| `00-应急方案详细手册.md` | https://apm.formalmath.internal | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://apm.formalmath.internal |
| `FormalMath-Enhanced/api/API_RELIABILITY_REPORT.md` | https://app.formalmath.com | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://app.formalmath.com |
| `00-安全最终审计报告.md` | https://app.formalmath.io | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://app.formalmath.io |
| `FormalMath-Enhanced/03-IMO-Competition/2011/Problem-03.md` | https://artofproblemsolving.com | 403 | https://artofproblemsolving.com |
| `FormalMath-Enhanced/03-IMO-Competition/IMO备赛指南.md` | https://artofproblemsolving.com/ | 403 | https://artofproblemsolving.com/ |
| `FormalMath-Enhanced/03-IMO-Competition/README.md` | https://artofproblemsolving.com/ | 403 | https://artofproblemsolving.com/ |
| `FormalMath-Enhanced/03-IMO-Competition/2010/Problem-02.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2011/Problem-01.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2011/Problem-06.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2012/Problem-01.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2012/Problem-03.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2012/Problem-05.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2013/Problem-05.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2014/Problem-01.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2014/Problem-03.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2014/Problem-04.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2014/Problem-06.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2015/Problem-01.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2015/Problem-03.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2015/Problem-04.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2015/Problem-06.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2018/Problem-03.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2018/Problem-06.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2020/Problem-03.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2020/Problem-05.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2021/Problem-01.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2021/Problem-02.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2021/Problem-04.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2021/Problem-05.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2021/Problem-06.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2022/Problem-04.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2022/Problem-06.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2023/Problem-01.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2023/Problem-05.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2024/Problem-01.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2024/Problem-05.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2025/Problem-01.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/2025/Problem-06.md` | https://artofproblemsolving.com/community/c6 | 403 | https://artofproblemsolving.com/community/c6 |
| `FormalMath-Enhanced/03-IMO-Competition/IMO备赛指南.md` | https://artofproblemsolving.com/community/c6_high_school_olympiads | 403 | https://artofproblemsolving.com/community/c6_high_school_olympiads |
| `FormalMath-Enhanced/03-IMO-Competition/README.md` | https://artofproblemsolving.com/community/c6_high_school_olympiads | 403 | https://artofproblemsolving.com/community/c6_high_school_olympiads |
| `FormalMath-Enhanced/03-IMO-Competition/2010/Problem-02.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2011/Problem-01.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2011/Problem-06.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2012/Problem-01.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2012/Problem-03.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2012/Problem-05.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2013/Problem-05.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2014/Problem-01.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2014/Problem-03.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2014/Problem-04.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2014/Problem-06.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2015/Problem-01.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2015/Problem-03.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2015/Problem-04.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2015/Problem-06.md` | https://artofproblemsolving.com/community/c6h | 403 | https://artofproblemsolving.com/community/c6h |
| `FormalMath-Enhanced/03-IMO-Competition/2006/Problem-01.md` | https://artofproblemsolving.com/community/c6h101488p572820 | 403 | https://artofproblemsolving.com/community/c6h101488p572820 |
| `FormalMath-Enhanced/03-IMO-Competition/2006/Problem-02.md` | https://artofproblemsolving.com/community/c6h101489p572822 | 403 | https://artofproblemsolving.com/community/c6h101489p572822 |
| `FormalMath-Enhanced/03-IMO-Competition/2006/Problem-03.md` | https://artofproblemsolving.com/community/c6h101490p572824 | 403 | https://artofproblemsolving.com/community/c6h101490p572824 |
| `FormalMath-Enhanced/03-IMO-Competition/2006/Problem-04.md` | https://artofproblemsolving.com/community/c6h101491p572825 | 403 | https://artofproblemsolving.com/community/c6h101491p572825 |
| `FormalMath-Enhanced/03-IMO-Competition/2006/Problem-06.md` | https://artofproblemsolving.com/community/c6h101493p572827 | 403 | https://artofproblemsolving.com/community/c6h101493p572827 |
| `FormalMath-Enhanced/03-IMO-Competition/2006/Problem-05.md` | https://artofproblemsolving.com/community/c6h101493p572829 | 403 | https://artofproblemsolving.com/community/c6h101493p572829 |
| `FormalMath-Enhanced/03-IMO-Competition/2016/Problem-01.md` | https://artofproblemsolving.com/community/c6h1263912p6575270 | 403 | https://artofproblemsolving.com/community/c6h1263912p6575270 |
| `FormalMath-Enhanced/03-IMO-Competition/2016/Problem-02.md` | https://artofproblemsolving.com/community/c6h1263913p6575275 | 403 | https://artofproblemsolving.com/community/c6h1263913p6575275 |
| `FormalMath-Enhanced/03-IMO-Competition/2016/Problem-03.md` | https://artofproblemsolving.com/community/c6h1263914p6575280 | 403 | https://artofproblemsolving.com/community/c6h1263914p6575280 |
| `FormalMath-Enhanced/03-IMO-Competition/2016/Problem-04.md` | https://artofproblemsolving.com/community/c6h1263915p6575285 | 403 | https://artofproblemsolving.com/community/c6h1263915p6575285 |
| `FormalMath-Enhanced/03-IMO-Competition/2016/Problem-05.md` | https://artofproblemsolving.com/community/c6h1263916p6575290 | 403 | https://artofproblemsolving.com/community/c6h1263916p6575290 |
| `FormalMath-Enhanced/03-IMO-Competition/2016/Problem-06.md` | https://artofproblemsolving.com/community/c6h1263917p6575295 | 403 | https://artofproblemsolving.com/community/c6h1263917p6575295 |
| `FormalMath-Enhanced/03-IMO-Competition/2017/Problem-01.md` | https://artofproblemsolving.com/community/c6h1480146p8633190 | 403 | https://artofproblemsolving.com/community/c6h1480146p8633190 |
| `FormalMath-Enhanced/03-IMO-Competition/2017/Problem-02.md` | https://artofproblemsolving.com/community/c6h1480147p8633196 | 403 | https://artofproblemsolving.com/community/c6h1480147p8633196 |
| `FormalMath-Enhanced/03-IMO-Competition/2017/Problem-03.md` | https://artofproblemsolving.com/community/c6h1480148p8633202 | 403 | https://artofproblemsolving.com/community/c6h1480148p8633202 |
| `FormalMath-Enhanced/03-IMO-Competition/2017/Problem-04.md` | https://artofproblemsolving.com/community/c6h1480149p8633208 | 403 | https://artofproblemsolving.com/community/c6h1480149p8633208 |
| `FormalMath-Enhanced/03-IMO-Competition/2017/Problem-05.md` | https://artofproblemsolving.com/community/c6h1480150p8633214 | 403 | https://artofproblemsolving.com/community/c6h1480150p8633214 |
| `FormalMath-Enhanced/03-IMO-Competition/2017/Problem-06.md` | https://artofproblemsolving.com/community/c6h1480151p8633220 | 403 | https://artofproblemsolving.com/community/c6h1480151p8633220 |
| `FormalMath-Enhanced/03-IMO-Competition/2007/Problem-01.md` | https://artofproblemsolving.com/community/c6h159838p893685 | 403 | https://artofproblemsolving.com/community/c6h159838p893685 |
| `FormalMath-Enhanced/03-IMO-Competition/2007/Problem-02.md` | https://artofproblemsolving.com/community/c6h159839p893686 | 403 | https://artofproblemsolving.com/community/c6h159839p893686 |
| `FormalMath-Enhanced/03-IMO-Competition/2007/Problem-04.md` | https://artofproblemsolving.com/community/c6h159841p893690 | 403 | https://artofproblemsolving.com/community/c6h159841p893690 |
| `FormalMath-Enhanced/03-IMO-Competition/2007/Problem-05.md` | https://artofproblemsolving.com/community/c6h159842p893691 | 403 | https://artofproblemsolving.com/community/c6h159842p893691 |
| `FormalMath-Enhanced/03-IMO-Competition/2007/Problem-06.md` | https://artofproblemsolving.com/community/c6h159843p893692 | 403 | https://artofproblemsolving.com/community/c6h159843p893692 |
| `FormalMath-Enhanced/03-IMO-Competition/2007/Problem-03.md` | https://artofproblemsolving.com/community/c6h163343p909372 | 403 | https://artofproblemsolving.com/community/c6h163343p909372 |
| `FormalMath-Enhanced/03-IMO-Competition/2018/Problem-01.md` | https://artofproblemsolving.com/community/c6h1664175p10570910 | 403 | https://artofproblemsolving.com/community/c6h1664175p10570910 |
| `FormalMath-Enhanced/03-IMO-Competition/2018/Problem-02.md` | https://artofproblemsolving.com/community/c6h1664176p10570915 | 403 | https://artofproblemsolving.com/community/c6h1664176p10570915 |
| `FormalMath-Enhanced/03-IMO-Competition/2010/Problem-01.md` | https://artofproblemsolving.com/community/c6h1935849 | 403 | https://artofproblemsolving.com/community/c6h1935849 |
| `FormalMath-Enhanced/03-IMO-Competition/2010/Problem-04.md` | https://artofproblemsolving.com/community/c6h1935927 | 403 | https://artofproblemsolving.com/community/c6h1935927 |
| `FormalMath-Enhanced/03-IMO-Competition/2008/Problem-01.md` | https://artofproblemsolving.com/community/c6h216645p1191685 | 403 | https://artofproblemsolving.com/community/c6h216645p1191685 |
| `FormalMath-Enhanced/03-IMO-Competition/2008/Problem-02.md` | https://artofproblemsolving.com/community/c6h216647p1191681 | 403 | https://artofproblemsolving.com/community/c6h216647p1191681 |
| `FormalMath-Enhanced/03-IMO-Competition/2008/Problem-03.md` | https://artofproblemsolving.com/community/c6h216648p1191678 | 403 | https://artofproblemsolving.com/community/c6h216648p1191678 |
| `FormalMath-Enhanced/03-IMO-Competition/2008/Problem-04.md` | https://artofproblemsolving.com/community/c6h216649p1191683 | 403 | https://artofproblemsolving.com/community/c6h216649p1191683 |
| `FormalMath-Enhanced/03-IMO-Competition/2008/Problem-05.md` | https://artofproblemsolving.com/community/c6h216650p1191679 | 403 | https://artofproblemsolving.com/community/c6h216650p1191679 |
| `FormalMath-Enhanced/03-IMO-Competition/2008/Problem-06.md` | https://artofproblemsolving.com/community/c6h216651p1191671 | 403 | https://artofproblemsolving.com/community/c6h216651p1191671 |
| `FormalMath-Enhanced/03-IMO-Competition/2009/Problem-01.md` | https://artofproblemsolving.com/community/c6h289113p1558432 | 403 | https://artofproblemsolving.com/community/c6h289113p1558432 |
| `FormalMath-Enhanced/03-IMO-Competition/2009/Problem-02.md` | https://artofproblemsolving.com/community/c6h289114p1558436 | 403 | https://artofproblemsolving.com/community/c6h289114p1558436 |
| `FormalMath-Enhanced/03-IMO-Competition/2009/Problem-04.md` | https://artofproblemsolving.com/community/c6h289114p1558436 | 403 | https://artofproblemsolving.com/community/c6h289114p1558436 |
| `FormalMath-Enhanced/03-IMO-Competition/2009/Problem-03.md` | https://artofproblemsolving.com/community/c6h289115p1558446 | 403 | https://artofproblemsolving.com/community/c6h289115p1558446 |
| `FormalMath-Enhanced/03-IMO-Competition/2009/Problem-05.md` | https://artofproblemsolving.com/community/c6h289116p1558455 | 403 | https://artofproblemsolving.com/community/c6h289116p1558455 |
| `FormalMath-Enhanced/03-IMO-Competition/2009/Problem-06.md` | https://artofproblemsolving.com/community/c6h289117p1558473 | 403 | https://artofproblemsolving.com/community/c6h289117p1558473 |
| `FormalMath-Enhanced/03-IMO-Competition/2024/Problem-05.md` | https://artofproblemsolving.com/community/c6h3327975p30747596 | 403 | https://artofproblemsolving.com/community/c6h3327975p30747596 |
| `FormalMath-Enhanced/03-IMO-Competition/2011/Problem-02.md` | https://artofproblemsolving.com/community/c6h418983 | 403 | https://artofproblemsolving.com/community/c6h418983 |
| `FormalMath-Enhanced/03-IMO-Competition/2012/Problem-02.md` | https://artofproblemsolving.com/community/c6h488344 | 403 | https://artofproblemsolving.com/community/c6h488344 |
| `FormalMath-Enhanced/03-IMO-Competition/2012/Problem-06.md` | https://artofproblemsolving.com/community/c6h488349 | 403 | https://artofproblemsolving.com/community/c6h488349 |
| `FormalMath-Enhanced/03-IMO-Competition/2013/Problem-01.md` | https://artofproblemsolving.com/community/c6h542994 | 403 | https://artofproblemsolving.com/community/c6h542994 |
| `project/00-项目全面批判性评价与改进计划-2025年11月30日.md` | https://blog.sina.com.cn/s/blog_635affba0100gfvp.html | 418 | https://blog.sina.com.cn/s/blog_635affba0100gfvp.html |
| `FormalMath-Enhanced/deployment/cdn/QUICKSTART.md` | https://cdn.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://cdn.formalmath.org |
| `docs/管理员手册/02-部署指南.md` | https://cdn.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://cdn.formalmath.org |
| `FormalMath-Enhanced/deployment/cdn/QUICKSTART.md` | https://cdn.formalmath.org/static/main.1234abcd.js | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://cdn.formalmath.org/static/main.1234abcd.js |
| `00-应急方案详细手册.md` | https://cdn.formalmath.org/static/main.js | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://cdn.formalmath.org/static/main.js |
| `ref/Books/00-ref-Books项目要求与权威对标全面梳理-2026年01月31日.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/00-权威对标与全面推进计划-2026年01月31日.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/Concept Mapping in Mathematics/01-历史发展/01-概念映射工具的发展与演变.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/Concept Mapping in Mathematics/06-思维表征方式/01-概念映射思维导图.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/Concept Mapping in Mathematics/07-最新研究进展/01-2024-2025最新研究综述.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `.vscode/README.md` | https://code.visualstudio.com/docs/languages/markdown | _ssl.c:999: The handshake operation timed out | https://code.visualstudio.com/docs/languages/markdown |
| `00-全局导航与快速参考.md` | https://coq.inria.fr/ | The read operation timed out | https://coq.inria.fr/ |
| `ref/Books/00-ref-Books项目要求与权威对标全面梳理-2026年01月31日.md` | https://ctl.stanford.edu/concept-mapping | 403 | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/00-权威对标与全面推进计划-2026年01月31日.md` | https://ctl.stanford.edu/concept-mapping | 403 | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/Concept Mapping in Mathematics/06-思维表征方式/01-概念映射思维导图.md` | https://ctl.stanford.edu/concept-mapping | 403 | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/Concept Mapping in Mathematics/06-思维表征方式/02-概念映射多维矩阵.md` | https://ctl.stanford.edu/concept-mapping | 403 | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/Concept Mapping in Mathematics/06-思维表征方式/03-概念映射应用决策树.md` | https://ctl.stanford.edu/concept-mapping | 403 | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/Concept Mapping in Mathematics/07-最新研究进展/01-2024-2025最新研究综述.md` | https://ctl.stanford.edu/concept-mapping | 403 | https://ctl.stanford.edu/concept-mapping |
| `00-应急方案详细手册.md` | https://dash.cloudflare.com | 403 | https://dash.cloudflare.com |
| `00-Wikipedia多语言对齐报告.md` | https://de.wikipedia.org/ | 403 | https://de.wikipedia.org/ |
| `FormalMath-Enhanced/06-Modern-Frontiers/SciML/mit-18.337j-notes.md` | https://diffeqflux.sciml.ai/ | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://diffeqflux.sciml.ai/ |
| `数学家理念体系/00-ONLINE-RESOURCES-ALIGNMENT.md` | https://dl.acm.org/ | 403 | https://dl.acm.org/ |
| `00-外部链接修复报告.md` | https://docker.com | _ssl.c:999: The handshake operation timed out | https://docker.com |
| `00-FormalMath项目质量白皮书.md` | https://docs.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://docs.formalmath.org |
| `00-外部链接修复报告.md` | https://docs.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://docs.formalmath.org |
| `docs/00-认知诊断系统使用指南.md` | https://docs.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://docs.formalmath.org |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https://docs.formalmath.org/api | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://docs.formalmath.org/api |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1002/hbm.460020402 | 403 | https://onlinelibrary.wiley.com/doi/10.1002/hbm.460020402 |
| `docs/10-应用数学/01-核心内容/信息论-香农编码定理-深度扩展.md` | https://doi.org/10.1002/j.1538-7305.1948.tb01338.x | 418 | https://ieeexplore.ieee.org/document/6773024 |
| `concept/view/07-国际数学教育研究/03-新加坡数学教育/03-新加坡数学教育.md` | https://doi.org/10.1007/s10763-009-9173-4 | 404 | https://doi.org/10.1007/s10763-009-9173-4 |
| `00-外部链接修复报告.md` | https://doi.org/10.1016/S0079-7421(08) | 404 | https://doi.org/10.1016/S0079-7421(08) |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1080/02643290244000239 | 403 | https://www.tandfonline.com/doi/abs/10.1080/02643290244000239 |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1093/oxfordhb/9780199642342.013.041 | 403 | https://academic.oup.com/edited-volume/34494/chapter/292679312 |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1207/s15516709cog0502_2 | 403 | https://onlinelibrary.wiley.com/doi/10.1207/s15516709cog0502_2 |
| `concept/view/07-国际数学教育研究/03-新加坡数学教育/03-新加坡数学教育.md` | https://doi.org/10.5951/jresematheduc.40.3.0282 | 403 | https://pubs.nctm.org/view/journals/jrme/40/3/article-p282.xml |
| `00-应急方案详细手册.md` | https://ecs.console.aliyun.com | The read operation timed out | https://ecs.console.aliyun.com |
| `00-EPFL数学课程对齐报告.md` | https://edu.epfl.ch/coursebook | 403 | https://edu.epfl.ch/coursebook/ |
| `docs/08-计算数学/00-国际课程对齐对照表.md` | https://ee364a.stanford.edu/ | timed out | https://ee364a.stanford.edu/ |
| `00-Wikipedia多语言对齐报告.md` | https://en.wikipedia.org/ | 403 | https://en.wikipedia.org/ |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://en.wikipedia.org/wiki/ | 403 | https://en.wikipedia.org/wiki/ |
| `concept/00-集合论视角-核心概念分析/21-概形-集合论视角分析.md` | https://en.wikipedia.org/wiki/Affine_scheme | _ssl.c:999: The handshake operation timed out | https://en.wikipedia.org/wiki/Affine_scheme |
| `数学家理念体系/格洛腾迪克数学理念/00-归档-2026年4月/00-待归档/07-现代视角与评价/02-历史地位的评价.md` | https://en.wikipedia.org/wiki/Alexander_Grothendieck | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Alexander_Grothendieck |
| `数学家理念体系/格洛腾迪克数学理念/00-归档-2026年4月/00-待归档/08-知识关联分析/03-跨学科的影响与关联.md` | https://en.wikipedia.org/wiki/Alexander_Grothendieck | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Alexander_Grothendieck |
| `数学家理念体系/格洛腾迪克数学理念/02-数学内容深度分析/06-其他数学贡献/02-对偶性与Grothendieck对偶定理.md` | https://en.wikipedia.org/wiki/Alexander_Grothendieck | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Alexander_Grothendieck |
| `docs/00-习题示例反例库/代数/ALG-234-代数综合1.md` | https://en.wikipedia.org/wiki/Algebra_(ring_theory) | _ssl.c:999: The handshake operation timed out | https://en.wikipedia.org/wiki/Algebra_(ring_theory) |
| `数学家理念体系/格洛腾迪克数学理念/00-待归档/02-数学内容深度分析/05-代数几何现代化/08-代数几何的统一框架.md` | https://en.wikipedia.org/wiki/Algebraic_geometry | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Algebraic_geometry |
| `数学家理念体系/格洛腾迪克数学理念/00-待归档/02-数学内容深度分析/05-代数几何现代化/12-代数几何的微分方法.md` | https://en.wikipedia.org/wiki/Algebraic_geometry | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Algebraic_geometry |
| `数学家理念体系/格洛腾迪克数学理念/00-待归档/02-数学内容深度分析/06-其他数学贡献/22-代数几何中的Langlands纲领基础.md` | https://en.wikipedia.org/wiki/Algebraic_geometry | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Algebraic_geometry |
| `数学家理念体系/格洛腾迪克数学理念/00-待归档/02-数学内容深度分析/06-其他数学贡献/24-代数几何中的微分几何方法.md` | https://en.wikipedia.org/wiki/Algebraic_geometry | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Algebraic_geometry |
| `数学家理念体系/笛卡尔数学理念/02-数学内容深度分析/03-坐标系统贡献/01-笛卡尔坐标系.md` | https://en.wikipedia.org/wiki/Analytic_geometry | The read operation timed out | https://en.wikipedia.org/wiki/Analytic_geometry |
| `数学家理念体系/柯西数学理念/04-历史与传记/03-学术合作与交流.md` | https://en.wikipedia.org/wiki/Augustin-Louis_Cauchy | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Augustin-Louis_Cauchy |
| `数学家理念体系/魏尔斯特拉斯数学理念/01-核心理论/05-数学写作与教育理念.md` | https://en.wikipedia.org/wiki/Berlin_School_of_Mathematics | 403 | https://en.wikipedia.org/wiki/Berlin_School_of_Mathematics |
| `数学家理念体系/狄利克雷数学理念/06-对比研究/02-与黎曼的对比.md` | https://en.wikipedia.org/wiki/Bernhard_Riemann | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Bernhard_Riemann |
| `数学家理念体系/雅可比数学理念/02-数学内容深度分析/03-核心贡献领域三.md` | https://en.wikipedia.org/wiki/Carl_Gustav_Jacob_Jacobi | _ssl.c:999: The handshake operation timed out | https://en.wikipedia.org/wiki/Carl_Gustav_Jacob_Jacobi |
| `数学家理念体系/雅可比数学理念/05-现代应用与拓展/02-在其他学科中的应用.md` | https://en.wikipedia.org/wiki/Carl_Gustav_Jacob_Jacobi | _ssl.c:999: The handshake operation timed out | https://en.wikipedia.org/wiki/Carl_Gustav_Jacob_Jacobi |
| `concept/00-范畴论视角-核心概念分析/03-自然数-范畴论视角分析.md` | https://en.wikipedia.org/wiki/Category_(mathematics) | _ssl.c:999: The handshake operation timed out | https://en.wikipedia.org/wiki/Category_(mathematics) |
| `数学家理念体系/格洛腾迪克数学理念/00-待归档/02-数学内容深度分析/01-范畴论与函子理论/19-范畴的纤维范畴与2-范畴.md` | https://en.wikipedia.org/wiki/Category_(mathematics) | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1016) | https://en.wikipedia.org/wiki/Category_(mathematics) |
| `concept/00-范畴论视角-核心概念分析/29-图-范畴论视角分析.md` | https://en.wikipedia.org/wiki/Category_of_graphs | 403 | https://en.wikipedia.org/wiki/Category_of_graphs |
| `concept/00-范畴论视角-核心概念分析/01-集合-范畴论视角分析.md` | https://en.wikipedia.org/wiki/Category_of_sets | The read operation timed out | https://en.wikipedia.org/wiki/Category_of_sets |
| `concept/00-范畴论视角-核心概念分析/14-连续-范畴论视角分析.md` | https://en.wikipedia.org/wiki/Category_of_topological_spaces | The read operation timed out | https://en.wikipedia.org/wiki/Category_of_topological_spaces |
| `concept/00-范畴论视角-核心概念分析/12-线性映射-范畴论视角分析.md` | https://en.wikipedia.org/wiki/Category_of_vector_spaces | The read operation timed out | https://en.wikipedia.org/wiki/Category_of_vector_spaces |

## 五、说明

- **确认失效**：`404`、不可解析主机、非瞬态 `4xx` 等，需要替换或删除。
- **不确定/瞬态**：`403/429` 频率限制、`5xx`、超时、SSL 握手异常等，建议人工复核或稍后重试。
- `301/302` 跳转后的目标若返回 `200`，视为可用。
- Wikidata 实体页因对批量 HEAD 敏感，已跳过校验。