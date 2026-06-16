---
title: Phase 1 全库外部链接校验报告
level: meta
processed_at: '2026-06-16T16:03:10.131869'
review_status: draft
---

# Phase 1 全库外部链接校验报告

**校验时间**: 2026年06月16日 16:03
**校验范围**: 全库 Markdown 文档（排除 node_modules / .git / dist / build / 00-归档 等）
**检查链接总数**: 22031
**确认失效链接数**: 302 | **不确定/瞬态链接数**: 2022
**涉及唯一 URL 数**: 2849

## 一、按文档分类统计

| 分类 | 检查链接数 | 确认失效 | 不确定/瞬态 |
|------|-----------|---------|------------|
| mathematicians | 9449 | 7 | 1531 |
| docs | 8577 | 52 | 120 |
| other | 1739 | 90 | 145 |
| FormalMath-Enhanced | 1076 | 137 | 140 |
| concept | 779 | 0 | 58 |
| project | 376 | 4 | 18 |
| FormalMath-Interactive | 35 | 12 | 10 |

## 二、确认失效链接按域名汇总（Top 30）

| 域名 | 失效数 |
|------|-------|
| leanprover-community.github.io | 90 |
| ncatlab.org | 61 |
| github.com | 27 |
| mathshistory.st-andrews.ac.uk | 24 |
| localhost:8001 | 13 |
| www.maths.cam.ac.uk | 7 |
|  | 6 |
| example.com | 5 |
| api.deepseek.com | 4 |
| www.d.umn.edu | 4 |
| stacks.math.columbia.edu | 4 |
| kconrad.math.uconn.edu | 3 |
| terrytao.wordpress.com | 3 |
| math.berkeley.edu | 2 |
| www.math.harvard.edu | 2 |
| localhost:3000 | 2 |
| localhost | 2 |
| nginx | 2 |
| lean-lang.org | 2 |
| localhost:8000 | 2 |
| fonts.googleapis.com | 2 |
| math.arizona.edu | 2 |
| www.merga.net.au | 2 |
| www.aare.edu.au | 2 |
| web.stanford.edu | 1 |
| math.technion.ac.il | 1 |
| www.s.u-tokyo.ac.jp | 1 |
| 10 | 1 |
| backend | 1 |
| www.mathinf.uni-heidelberg.de | 1 |

## 三、确认失效链接清单（前 500 条）

| 文档路径 | 原链接 | 状态码 | 最终 URL |
|----------|--------|--------|----------|
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | http:// | no host given | http:// |
| `00-外部链接修复报告.md` | http://10 | [Errno 11001] getaddrinfo failed | http://10 |
| `docs/管理员手册/02-部署指南.md` | http://adaptive/ | [Errno 11001] getaddrinfo failed | http://adaptive/ |
| `FormalMath-Enhanced/monitoring/docs/TROUBLESHOOTING.md` | http://api:8000/metrics | [Errno 11001] getaddrinfo failed | http://api:8000/metrics |
| `docs/管理员手册/02-部署指南.md` | http://assessment/ | [Errno 11001] getaddrinfo failed | http://assessment/ |
| `00-外部链接修复报告.md` | http://backend | [Errno 11001] getaddrinfo failed | http://backend |
| `docs/管理员手册/02-部署指南.md` | http://cognitive_diagnosis/ | [Errno 11001] getaddrinfo failed | http://cognitive_diagnosis/ |
| `00-外部链接修复报告.md` | http://localhost | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost |
| `FormalMath-Enhanced/DEPLOYMENT.md` | http://localhost | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost |
| `00-外部链接修复报告.md` | http://localhost:3000 | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:3000 |
| `FormalMath-Enhanced/monitoring/docs/README.md` | http://localhost:3000 | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:3000 |
| `FormalMath-Enhanced/evaluation-system/00-优化建议.md` | http://localhost:8000/api/evaluation/assess | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8000/api/evaluation/assess |
| `FormalMath-Enhanced/cognitive-diagnosis/00-优化建议.md` | http://localhost:8000/health | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8000/health |
| `00-AI辅助学习系统集成报告.md` | http://localhost:8001 | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001 |
| `00-AI辅助学习系统集成报告.md` | http://localhost:8001/api/v1/ai-assistant | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant |
| `FormalMath-Enhanced/ai-assistant/docs/API.md` | http://localhost:8001/api/v1/ai-assistant | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant |
| `00-AI辅助学习系统集成报告.md` | http://localhost:8001/api/v1/ai-assistant/explain | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/explain |
| `FormalMath-Enhanced/ai-assistant/README.md` | http://localhost:8001/api/v1/ai-assistant/explain | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/explain |
| `00-AI辅助学习系统集成报告.md` | http://localhost:8001/api/v1/ai-assistant/learning-advice | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/learning-advice |
| `FormalMath-Enhanced/ai-assistant/README.md` | http://localhost:8001/api/v1/ai-assistant/learning-advice | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/learning-advice |
| `00-AI辅助学习系统集成报告.md` | http://localhost:8001/api/v1/ai-assistant/proof-hint | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/proof-hint |
| `FormalMath-Enhanced/ai-assistant/README.md` | http://localhost:8001/api/v1/ai-assistant/proof-hint | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/api/v1/ai-assistant/proof-hint |
| `00-AI辅助学习系统集成报告.md` | http://localhost:8001/docs | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/docs |
| `FormalMath-Enhanced/ai-assistant/README.md` | http://localhost:8001/docs | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/docs |
| `00-AI辅助学习系统集成报告.md` | http://localhost:8001/redoc | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/redoc |
| `FormalMath-Enhanced/ai-assistant/README.md` | http://localhost:8001/redoc | [WinError 10061] 由于目标计算机积极拒绝，无法连接。 | http://localhost:8001/redoc |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://math.arizona.edu/~cemela/spanish/content/workingpapers/UsingTwoLanguages.pdf | 404 | https://archive.math.arizona.edu/cemela/spanish/content/workingpapers/UsingTwoLanguages.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://math.arizona.edu/~cemela/spanish/content/workingpapers/UsingTwoLanguages.pdf | 404 | https://archive.math.arizona.edu/cemela/spanish/content/workingpapers/UsingTwoLanguages.pdf |
| `FormalMath-Enhanced/DEPLOYMENT_OPTIMIZATION_FINAL.md` | http://nginx | [Errno 11001] getaddrinfo failed | http://nginx |
| `FormalMath-Enhanced/PRODUCTION_CHECKLIST_FINAL.md` | http://nginx | [Errno 11001] getaddrinfo failed | http://nginx |
| `FormalMath-Enhanced/monitoring/docs/TROUBLESHOOTING.md` | http://prometheus:9090/api/v1/status/targets | [Errno 11001] getaddrinfo failed | http://prometheus:9090/api/v1/status/targets |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.aare.edu.au/06pap/afa06011.pdf | 404 | https://www.aare.edu.au/06pap/afa06011.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.aare.edu.au/06pap/afa06011.pdf | 404 | https://www.aare.edu.au/06pap/afa06011.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.merga.net.au/documents/RP12007.pdf | 404 | http://www.merga.net.au/documents/RP12007.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.merga.net.au/documents/RP12007.pdf | 404 | http://www.merga.net.au/documents/RP12007.pdf |
| `research/06-思维表征/表征方式/03-矩阵对比.md` | http://www.pz.harvard.edu/thinking-routines | 404 | http://www.pz.harvard.edu/thinking-routines |
| `00-外部链接修复报告.md` | https:// | no host given | https:// |
| `FormalMath-Enhanced/api/NOTIFICATION_SYSTEM_SUMMARY.md` | https:// | no host given | https:// |
| `FormalMath-Enhanced/api/app/notifications/README.md` | https:// | no host given | https:// |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https:// | no host given | https:// |
| `docs/链接维护指南.md` | https:// | no host given | https:// |
| `docs/管理员手册/05-安全管理.md` | https://$server_name$request_uri | [Errno 11001] getaddrinfo failed | https://$server_name$request_uri |
| `00-移动端适配实施报告.md` | https://ant.design/docs/spec/mobile | 404 | https://ant.design/docs/spec/mobile |
| `00-AI辅助学习系统集成报告.md` | https://api.deepseek.com | 401 | https://api.deepseek.com |
| `FormalMath-Enhanced/05-AI-Formalization/07-Code-Examples.md` | https://api.deepseek.com | 401 | https://api.deepseek.com |
| `FormalMath-Enhanced/ai-assistant/README.md` | https://api.deepseek.com | 401 | https://api.deepseek.com |
| `FormalMath-Enhanced/05-AI-Formalization/tools/README.md` | https://api.deepseek.com/v1 | 401 | https://api.deepseek.com/v1 |
| `.github/CI_CD_GUIDE.md` | https://api.github.com/repos/formalmath/formalmath/actions/workflows/test.yml/dispatches | 404 | https://api.github.com/repos/formalmath/formalmath/actions/workflows/test.yml/dispatches |
| `FormalMath-Enhanced/05-AI-Formalization/05-AlphaProof.md` | https://deepmind.google/discover/blog/alphaproof-achieves-silver-medal-level-in-imo/ | 404 | https://deepmind.google/discover/blog/alphaproof-achieves-silver-medal-level-in-imo/ |
| `ref/Books/AbstractAlgebra/Paulsen W. Abstract Algebra. An Interactive Approach 3ed 2025/full.md` | https://dl.google.com/linux/direct/google-chrome-stable_current_amd64deb | 404 | https://dl.google.com/linux/direct/google-chrome-stable_current_amd64deb |
| `FormalMath-Enhanced/api/API_RELIABILITY_REPORT.md` | https://docs.python.org/3/howto/performance.html | 404 | https://docs.python.org/3/howto/performance.html |
| `FormalMath-Interactive/src/components/Collaboration/README.md` | https://example.com/avatar.jpg | 404 | https://example.com/avatar.jpg |
| `FormalMath-Interactive/docs/Social-Media-Implementation-Report.md` | https://example.com/concept/algebra | 404 | https://example.com/concept/algebra |
| `FormalMath-Interactive/docs/Social-Media-Implementation-Report.md` | https://example.com/page | 404 | https://example.com/page |
| `FormalMath-Interactive/docs/Social-Media-Integration.md` | https://example.com/page | 404 | https://example.com/page |
| `FormalMath-Interactive/src/components/SocialFeatures/README.md` | https://example.com/page | 404 | https://example.com/page |
| `FormalMath-Interactive/00-移动端PWA适配报告.md` | https://fonts.googleapis.com | 404 | https://fonts.googleapis.com |
| `FormalMath-Interactive/docs/SEO-Implementation-Report.md` | https://fonts.googleapis.com | 404 | https://fonts.googleapis.com |
| `FormalMath-Interactive/docs/SEO-Implementation-Report.md` | https://fonts.gstatic.com | 404 | https://fonts.gstatic.com |
| `FormalMath-Enhanced/DEPLOYMENT_OPTIMIZATION_SUMMARY.md` | https://github.com/FormalMath-enhanced.git | 404 | https://github.com/FormalMath-enhanced.git |
| `FormalMath-Enhanced/OPERATIONS_MANUAL.md` | https://github.com/FormalMath-enhanced.git | 404 | https://github.com/FormalMath-enhanced.git |
| `FormalMath-Enhanced/QUICKSTART.md` | https://github.com/FormalMath-enhanced.git | 404 | https://github.com/FormalMath-enhanced.git |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/actions | 404 | https://github.com/FormalMath/actions |
| `README.en.md` | https://github.com/FormalMath/actions/workflows/build.yml | 404 | https://github.com/FormalMath/actions/workflows/build.yml |
| `README.en.md` | https://github.com/FormalMath/actions/workflows/deploy.yml | 404 | https://github.com/FormalMath/actions/workflows/deploy.yml |
| `README.en.md` | https://github.com/FormalMath/actions/workflows/security.yml | 404 | https://github.com/FormalMath/actions/workflows/security.yml |
| `README.en.md` | https://github.com/FormalMath/actions/workflows/test.yml | 404 | https://github.com/FormalMath/actions/workflows/test.yml |
| `output/marketing/05-新闻稿模板.md` | https://github.com/FormalMath/blob/main/CONTRIBUTING.md | 404 | https://github.com/FormalMath/blob/main/CONTRIBUTING.md |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/deployments | 404 | https://github.com/FormalMath/deployments |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/releases | 404 | https://github.com/FormalMath/releases |
| `00-安全最终审计报告.md` | https://github.com/FormalMath/security | 404 | https://github.com/FormalMath/security |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/security/advisories | 404 | https://github.com/FormalMath/security/advisories |
| `SECURITY.md` | https://github.com/FormalMath/security/advisories | 404 | https://github.com/FormalMath/security/advisories |
| `FormalMath-Interactive/DEPLOY.md` | https://github.com/FormalMath/wiki | 404 | https://github.com/FormalMath/wiki |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/workflows/Build/badge.svg | 404 | https://github.com/FormalMath/workflows/Build/badge.svg |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/workflows/CodeQL/badge.svg | 404 | https://github.com/FormalMath/workflows/CodeQL/badge.svg |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/workflows/Deploy/badge.svg | 404 | https://github.com/FormalMath/workflows/Deploy/badge.svg |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/workflows/Quality%20Assurance/badge.svg | 404 | https://github.com/FormalMath/workflows/Quality%20Assurance/badge.svg |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/workflows/Release/badge.svg | 404 | https://github.com/FormalMath/workflows/Release/badge.svg |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/workflows/Security/badge.svg | 404 | https://github.com/FormalMath/workflows/Security/badge.svg |
| `.github/WORKFLOW_STATUS.md` | https://github.com/FormalMath/workflows/Test/badge.svg | 404 | https://github.com/FormalMath/workflows/Test/badge.svg |
| `FormalMath-Enhanced/05-AI-Formalization/01-KELPS.md` | https://github.com/deepseek-ai/kelps | 404 | https://github.com/deepseek-ai/kelps |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https://github.com/formalmath/api/issues | 404 | https://github.com/formalmath/api/issues |
| `ref/nLab-同伦类型论-中文解读.md` | https://github.com/gebner/lean-hott | 404 | https://github.com/gebner/lean-hott |
| `FormalMath-Enhanced/05-AI-Formalization/03-LeanAgent.md` | https://github.com/lean-agent/leanagent | 404 | https://github.com/lean-agent/leanagent |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/GraphTheory/four-color-theorem.md` | https://github.com/leanprover-community/fourcolor | 404 | https://github.com/leanprover-community/fourcolor |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/maschke-theorem.md` | https://groupprops.subwiki.org/wiki/Maschke%27s_theorem_for_finite_groups | 404 | https://groupprops.subwiki.org/wiki/Maschke%27s_theorem_for_finite_groups |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/galois-fundamental-theorem.md` | https://kconrad.math.uconn.edu/blurbs/galoistheory/galoiscorresp.pdf | 404 | https://kconrad.math.uconn.edu/blurbs/galoistheory/galoiscorresp.pdf |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/separable-extension.md` | https://kconrad.math.uconn.edu/blurbs/galoistheory/separable.pdf | 404 | https://kconrad.math.uconn.edu/blurbs/galoistheory/separable.pdf |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/structure-theorem-fg-modules.md` | https://kconrad.math.uconn.edu/blurbs/linmultialg/modulesoverpids.pdf | 404 | https://kconrad.math.uconn.edu/blurbs/linmultialg/modulesoverpids.pdf |
| `FormalMath-Enhanced/lean4/FormalMath/00-Lean4-Mathlib4对齐报告.md` | https://lean-lang.org/api/ | 404 | https://lean-lang.org/api/ |
| `FormalMath-Enhanced/05-AI-Formalization/07-Code-Examples.md` | https://lean-lang.org/api/lean4/ | 404 | https://lean-lang.org/api/lean4/ |
| `ref/Stacks-Tag-解读/Tag-05QI-导出范畴.md` | https://leanprover-community.github.io/api/latest/Mathlib-Algebra-Homology.html | 404 | https://leanprover-community.github.io/api/latest/Mathlib-Algebra-Homology.html |
| `ref/Stacks-Tag-解读/Tag-01XI-仿射对角线概形上同调消失.md` | https://leanprover-community.github.io/api/latest/Mathlib-AlgebraicGeometry.html | 404 | https://leanprover-community.github.io/api/latest/Mathlib-AlgebraicGeometry.html |
| `ref/Stacks-Tag-解读/Tag-00DV-Nakayama引理.md` | https://leanprover-community.github.io/api/latest/Mathlib-RingTheory-Nakayama.html | 404 | https://leanprover-community.github.io/api/latest/Mathlib-RingTheory-Nakayama.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/universal-coefficient-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Homology.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Homology.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/schur-lemma.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/SimpleModule.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/SimpleModule.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/tensor-product-properties.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/TensorProduct/Basic.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Module/TensorProduct/Basic.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AlgebraicGeometry/blow-up-resolution.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AlgebraicGeometry/bezout-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Bezout.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/Bezout.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AlgebraicTopology/mayer-vietoris-sequence.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/poincare-duality.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/Cohomology.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/Cohomology.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/fundamental-group-circle.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/van-kampen-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/VanKampen.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/FundamentalGroupoid/VanKampen.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/jordan-curve-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/Homotopy/Sphere.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/Homotopy/Sphere.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/borsuk-ulam-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/HomotopyGroup.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/HomotopyGroup.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/mayer-vietoris-sequence.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/HomotopyGroup.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/HomotopyGroup.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AlgebraicTopology/mayer-vietoris-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/MayerVietoris.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/MayerVietoris.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AlgebraicTopology/lefechtz-fixed-point-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/inverse-function-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Inverse.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Inverse.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/riemann-mapping-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Conformal/Basic.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Conformal/Basic.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/maximum-modulus-principle.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/MaximumModulus.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/MaximumModulus.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/residue-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Residue.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Residue.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/runge-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Runge.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/Runge.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/schwarz-lemma.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/SchwarzLemma.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/SchwarzLemma.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/plancherel-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Plancherel.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Plancherel.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AdvancedAnalysis/closed-graph-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Banach.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Banach.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AdvancedAnalysis/open-mapping-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Banach.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Banach.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/open-mapping-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/BanachSteinhaus.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/BanachSteinhaus.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/matrix-exponential-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Exponential.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/Exponential.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AdvancedAnalysis/hahn-banach-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/HahnBanach.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/HahnBanach.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/hahn-banach-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/HahnBanach/Extension.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/NormedSpace/HahnBanach/Extension.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/mean-value-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Calculus/MeanValue.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Calculus/MeanValue.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/five-lemma.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Five.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Abelian/Five.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/GraphTheory/max-flow-min-cut.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Optimization/Flow.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Optimization/Flow.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/GraphTheory/menger-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Connectivity.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Connectivity.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/GraphTheory/planar-graph-euler-formula.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Planarity.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Planarity.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/GraphTheory/ramsey-number-exists.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Ramsey.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Ramsey.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/GraphTheory/turan-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Turan.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Turan.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/stokes-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/classical-stokes-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Basic.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Basic.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Geometry/stokes-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Basic.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Basic.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Geometry/gauss-bonnet-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Curvature/GaussBonnet.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Curvature/GaussBonnet.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Geometry/hopf-rinow-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/RiemannianManifold/HopfRinow.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/RiemannianManifold/HopfRinow.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Geometry/darboux-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Symplectic/Basic.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Symplectic/Basic.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/jordan-holder-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/CompositionSeries.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/CompositionSeries.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/first-isomorphism-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/QuotientGroup.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/QuotientGroup.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/fredholm-alternative.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/rank-nullity-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/FiniteDimensional.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/gram-schmidt-orthogonalization.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/GramSchmidt.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/GramSchmidt.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/jordan-normal-form.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/JordanNormalForm.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/JordanNormalForm.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/determinant-product.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/polar-decomposition.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PolarDecomposition.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PolarDecomposition.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/qr-decomposition.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/QR.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/QR.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/schur-decomposition.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Schur.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Schur.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/svd-decomposition.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SVD.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SVD.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/svd-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SVD.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SVD.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/spectral-theorem-normal.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SpectralTheorem.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SpectralTheorem.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LinearAlgebra/spectral-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SpectralTheorem.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/SpectralTheorem.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LogicFoundation/diagonal-lemma.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Godel/Diagonal.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Godel/Diagonal.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/dominated-convergence-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Probability/expectation-linearity.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/fundamental-theorem-calculus.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/integration-by-parts-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/IntervalIntegral.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Probability/markov-inequality.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/change-of-variables-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/SetIntegral.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/SetIntegral.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/ham-sandwich-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Haar.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Haar.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/radon-nikodym-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/RadonNikodym.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/RadonNikodym.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/riesz-representation-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/RieszRepresentation.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/RieszRepresentation.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/LogicFoundation/godel-completeness-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Completeness.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Completeness.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/NumberTheory/mertens-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/ArithmeticFunction.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/NumberTheory/dirichlet-theorem-arithmetic-progression.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletTheorem.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/DirichletTheorem.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/NumberTheory/mobius-inversion-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Moebius.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Moebius.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/NumberTheory/legendre-formula.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Padics/PadicVal.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Padics/PadicVal.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/NumberTheory/euler-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Totient.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Totient.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Probability/central-limit-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Probability/jensen-inequality.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Probability/chebyshev-inequality.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Probability/variance-sum-independent.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/wedderburn-artin-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Artinian.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/noether-normalization.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Finiteness.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Finiteness.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/nakayama-lemma.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/LocalRing.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/LocalRing.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/chinese-remainder-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Quotient.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/hilbert-basis-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/noether-normalization-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Noetherian.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/baire-category-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Baire/CompleteSpace.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Baire/CompleteSpace.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/stone-weierstrass-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousFunction/Algebra.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousFunction/Algebra.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/weierstrass-approximation.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousFunction/Polynomial.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousFunction/Polynomial.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Calculus/brouwer-fixed-point-ball.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FixedPoint.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FixedPoint.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/brouwer-fixed-point-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FixedPoint.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/FixedPoint.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Topology/metrization-theorem.md` | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Metrizable.html | 404 | https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Metrizable.html |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/snake-lemma.md` | https://leanprover-community.github.io/mathlib4_docs/ShortComplex/Basic.html | 404 | https://leanprover-community.github.io/mathlib4_docs/ShortComplex/Basic.html |
| `00-外部链接修复报告.md` | https://math.berkeley.edu/math256-fall18-spring19/ | 404 | https://math.berkeley.edu/math256-fall18-spring19/ |
| `project/v2-quality-rewrite/workspaces/courses/stanford-foag/T010-syllabus-deconstruction/task-report.md` | https://math.berkeley.edu/math256-fall18-spring19/ | 404 | https://math.berkeley.edu/math256-fall18-spring19/ |
| `00-Technion数学课程对齐报告.md` | https://math.technion.ac.il/en/undergraduate-courses/ | 404 | https://math.technion.ac.il/en/undergraduate-courses/ |
| `docs/12-学术资源/04-耶鲁大学数学课程对齐报告.md` | https://math.yale.edu/undergraduate-program | 404 | https://math.yale.edu/undergraduate-program |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Hall.Marshall/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Hall.Marshall/ |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AdvancedAlgebra/noether-normalization.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/noether-normalization-lemma.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Algebra/noether-normalization-theorem.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `docs/00-习题示例反例库/代数/ALG-046-Noether模与Artin模.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `docs/00-习题示例反例库/代数/ALG-107-Noether正规化定理.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `docs/00-核心概念理解三问/11-核心定理多表征/42-Noether定理-五种表征.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `docs/02-代数结构/交换代数/02-Noetherian环与Artinian环.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `ref/Stacks-Tag-解读/Tag-00DT-Noetherian拓扑空间.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `ref/Stacks-Tag-解读/Tag-00DX-Noetherian环.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `ref/Stacks-Tag-解读/Tag-00GV-Noether正规化定理.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/00-归档-2026年4月-其他数学家/庞加莱数学理念/02-数学内容深度分析/05-数学物理/19-对称性与守恒定律.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `数学家理念体系/格洛腾迪克数学理念/00-待归档/02-数学内容深度分析/02-概形理论/10-Noether概形与有限性.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Noether/ |
| `research/09-数学人物/现代数学家/06-舒尔茨.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ |
| `数学家理念体系/肖尔策数学理念/02-数学内容深度分析/01-完美oid空间.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ |
| `数学家理念体系/肖尔策数学理念/02-数学内容深度分析/02-p进Hodge理论.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ |
| `数学家理念体系/肖尔策数学理念/02-数学内容深度分析/03-凝聚态数学.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ |
| `数学家理念体系/肖尔策数学理念/02-数学内容深度分析/04-朗兰兹纲领几何化/01-Fargues-Scholze几何化.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Scholze/ |
| `research/09-数学人物/现代数学家/07-张益唐.md` | https://mathshistory.st-andrews.ac.uk/Biographies/Zhang_Yitang/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/Zhang_Yitang/ |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AdvancedAnalysis/von-neumann-algebra.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `docs/00-数学史/11-John von Neumann传记.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `docs/03-分析学/03-泛函分析-扩展/06-C代数与von Neumann代数-深度扩展版.md` | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ | 404 | https://mathshistory.st-andrews.ac.uk/Biographies/von-Neumann/ |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://mathshistory.st-andrews.ac.uk/\Biographies/Adleman/ | 404 | https://mathshistory.st-andrews.ac.uk/%5CBiographies/Adleman/ |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://mathshistory.st-andrews.ac.uk/\Biographies/Lagrange/ | 404 | https://mathshistory.st-andrews.ac.uk/%5CBiographies/Lagrange/ |
| `FormalMath-Enhanced/01-MSC-Coding/00-MSC2020-编码标准说明.md` | https://msc2020.org/resources/MSC/2020/MSC2020.rdf | 404 | https://msc2020.org/resources/MSC/2020/MSC2020.rdf |
| `docs/00-知识层次体系/L4-前沿研究层/03-数论前沿/02-BSD猜想.md` | https://ncatlab.org/nlab/show/Birch-Swinnerton-Dyer+conjecture | 404 | https://ncatlab.org/nlab/show/Birch-Swinnerton-Dyer+conjecture |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/NumberTheory/dirichlet-theorem-arithmetic-progression.md` | https://ncatlab.org/nlab/show/Dirichlet's+theorem | 404 | https://ncatlab.org/nlab/show/Dirichlet's+theorem |
| `数学家理念体系/狄利克雷数学理念/02-数学内容深度分析/01-数论贡献/01-狄利克雷定理.md` | https://ncatlab.org/nlab/show/Dirichlet's+theorem | 404 | https://ncatlab.org/nlab/show/Dirichlet's+theorem |
| `ref/Stacks-Tag-解读/Tag-013Z-K-内射复形.md` | https://ncatlab.org/nlab/show/K-injective+complex | 404 | https://ncatlab.org/nlab/show/K-injective+complex |
| `ref/Stacks-Tag-解读/Tag-00GV-Noether正规化定理.md` | https://ncatlab.org/nlab/show/Noether+normalization+lemma | 404 | https://ncatlab.org/nlab/show/Noether+normalization+lemma |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AdvancedAnalysis/plancherel-theorem.md` | https://ncatlab.org/nlab/show/Plancherel+theorem | 404 | https://ncatlab.org/nlab/show/Plancherel+theorem |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AdvancedAnalysis/elliptic-regularity.md` | https://ncatlab.org/nlab/show/Schauder+estimate | 404 | https://ncatlab.org/nlab/show/Schauder+estimate |
| `ref/Stacks-Tag-解读/Tag-01X8-仿射概形上同调.md` | https://ncatlab.org/nlab/show/Serre%27s+criterion+for+affineness | 404 | https://ncatlab.org/nlab/show/Serre%27s+criterion+for+affineness |
| `ref/Stacks-Tag-解读/Tag-01YG-Serre消失定理.md` | https://ncatlab.org/nlab/show/Serre+vanishing+theorem | 404 | https://ncatlab.org/nlab/show/Serre+vanishing+theorem |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/AdvancedAnalysis/sobolev-embedding.md` | https://ncatlab.org/nlab/show/Sobolev+embedding+theorem | 404 | https://ncatlab.org/nlab/show/Sobolev+embedding+theorem |
| `ref/Stacks-Tag-解读/Tag-01X8-仿射概形上同调.md` | https://ncatlab.org/nlab/show/cohomology+of+a+sheaf+of+modules | 404 | https://ncatlab.org/nlab/show/cohomology+of+a+sheaf+of+modules |
| `ref/Stacks-Tag-解读/Tag-02O3-射影空间上同调计算.md` | https://ncatlab.org/nlab/show/cohomology+of+projective+space | 404 | https://ncatlab.org/nlab/show/cohomology+of+projective+space |
| `ref/Stacks-Tag-解读/Tag-02SK-离散赋值环惯性群.md` | https://ncatlab.org/nlab/show/decomposition+group | 404 | https://ncatlab.org/nlab/show/decomposition+group |
| `ref/Stacks-Tag-解读/Tag-00KD-Krull维数.md` | https://ncatlab.org/nlab/show/dimension+of+a+scheme | 404 | https://ncatlab.org/nlab/show/dimension+of+a+scheme |
| `ref/Stacks-Tag-解读/Tag-00GV-Noether正规化定理.md` | https://ncatlab.org/nlab/show/finite+morphism | 404 | https://ncatlab.org/nlab/show/finite+morphism |
| `ref/Stacks-Tag-解读/Tag-00KD-Krull维数.md` | https://ncatlab.org/nlab/show/height+of+a+prime+ideal | 404 | https://ncatlab.org/nlab/show/height+of+a+prime+ideal |
| `ref/Stacks-Tag-解读/Tag-02SK-离散赋值环惯性群.md` | https://ncatlab.org/nlab/show/inertia+group | 404 | https://ncatlab.org/nlab/show/inertia+group |
| `ref/Stacks-Tag-解读/Tag-00GV-Noether正规化定理.md` | https://ncatlab.org/nlab/show/integral+extension | 404 | https://ncatlab.org/nlab/show/integral+extension |
| `ref/Stacks-Tag-解读/Tag-01LC-拟凝聚层定义.md` | https://ncatlab.org/nlab/show/module+over+a+ringed+space | 404 | https://ncatlab.org/nlab/show/module+over+a+ringed+space |
| `docs/03-分析学/最优控制理论-深度版.md` | https://ncatlab.org/nlab/show/optimal+control | 404 | https://ncatlab.org/nlab/show/optimal+control |
| `docs/concept-mindmaps/optimal-control.md` | https://ncatlab.org/nlab/show/optimal+control | 404 | https://ncatlab.org/nlab/show/optimal+control |
| `docs/inference-trees/app-ctrl-pontryagin-principle.md` | https://ncatlab.org/nlab/show/optimal+control | 404 | https://ncatlab.org/nlab/show/optimal+control |
| `docs/应用案例库/03-工程学应用/06-最优控制理论.md` | https://ncatlab.org/nlab/show/optimal+control | 404 | https://ncatlab.org/nlab/show/optimal+control |
| `FormalMath-Interactive/SEO-IMPLEMENTATION-SUMMARY.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `FormalMath-Interactive/docs/Internationalization-Optimization.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/00-交叉引用网络/01-导航优化方案.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/00-表征实例库/表征实例-057-优化问题的对偶理论.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/08-计算数学/02-优化理论-增强版.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/08-计算数学/02-优化理论.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/08-计算数学/03-优化算法-增强版.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/08-计算数学/03-优化算法.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/08-计算数学/10-优化算法.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/10-应用数学/01-核心内容/优化理论进阶-深度版.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/11-数学应用/13-神经网络优化的数学基础.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/21-最优化/01-基础概念.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/21-最优化/02-凸优化-完整版.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/21-最优化/02-凸优化-工业级深化版.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/21-最优化/02-核心定理.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/21-最优化/03-实战问题.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/21-最优化/INDEX.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/21-最优化/最优化-实例与代码补充.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/concept-mindmaps/app-ds-04-优化算法.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/concept-mindmaps/convex-optimization.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/concept-mindmaps/cross-cs-machine-learning.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/concept-mindmaps/cross-econ-optimization.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/concept-mindmaps/cross-eng-operations-research.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/concept-mindmaps/ml-07-optimization-algorithms.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/concept-mindmaps/stochastic-optimization.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/visualizations/思维导图/概念/应用数学/优化基础.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/visualizations/思维导图/概念/应用数学/变分优化.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/应用案例库/02-计算机科学应用/09-编译器优化.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/应用案例库/人工智能机器学习/机器学习中的梯度下降-深度版.md` | https://ncatlab.org/nlab/show/optimization | 404 | https://ncatlab.org/nlab/show/optimization |
| `docs/00-知识层次体系/L4-前沿研究层/03-数论前沿/01-p进Langlands纲领.md` | https://ncatlab.org/nlab/show/p-adic+Langlands+program | 404 | https://ncatlab.org/nlab/show/p-adic+Langlands+program |
| `docs/06-概率论与统计/01-概率论基础/11-回归分析-增强版.md` | https://ncatlab.org/nlab/show/regression+analysis | 404 | https://ncatlab.org/nlab/show/regression+analysis |
| `docs/06-概率论与统计/06-回归分析/01-线性回归.md` | https://ncatlab.org/nlab/show/regression+analysis | 404 | https://ncatlab.org/nlab/show/regression+analysis |
| `docs/concept-mindmaps/03-回归分析-思维导图.md` | https://ncatlab.org/nlab/show/regression+analysis | 404 | https://ncatlab.org/nlab/show/regression+analysis |
| `docs/10-应用数学/强化学习数学-基础.md` | https://ncatlab.org/nlab/show/reinforcement+learning | 404 | https://ncatlab.org/nlab/show/reinforcement+learning |
| `docs/concept-mindmaps/app-ds-06-强化学习.md` | https://ncatlab.org/nlab/show/reinforcement+learning | 404 | https://ncatlab.org/nlab/show/reinforcement+learning |
| `docs/concept-mindmaps/ml-05-reinforcement-learning.md` | https://ncatlab.org/nlab/show/reinforcement+learning | 404 | https://ncatlab.org/nlab/show/reinforcement+learning |
| `docs/应用案例库/07-人工智能机器学习/02-强化学习基础.md` | https://ncatlab.org/nlab/show/reinforcement+learning | 404 | https://ncatlab.org/nlab/show/reinforcement+learning |
| `ref/Stacks-Tag-解读/Tag-02O3-射影空间上同调计算.md` | https://ncatlab.org/nlab/show/twisted+sheaf | 404 | https://ncatlab.org/nlab/show/twisted+sheaf |
| `FormalMath-Enhanced/05-AI-Formalization/02-DeepSeek-Math.md` | https://openwebmath.github.io/ | 404 | https://openwebmath.github.io/ |
| `project/v2-quality-rewrite/workspaces/courses/harvard-232br/T009-syllabus-deconstruction/task-report.md` | https://people.maths.ox.ac.uk/liu/notes/s17-algebraic-geometry.pdf | 404 | https://people.maths.ox.ac.uk/liu/notes/s17-algebraic-geometry.pdf |
| `FormalMath-Enhanced/DEPLOYMENT.md` | https://redis.io/docs/manual/persistence/ | 404 | https://redis.io/docs/latest/manual/persistence/ |
| `ref/Stacks-Tag-解读/Tag-01V5-光滑态射.md` | https://stacks.math.columbia.edu/chapter/01QY | 404 | https://stacks.math.columbia.edu/chapter/01QY |
| `ref/Stacks-Tag-解读/Tag-07GJ-晶体上同调与de-Rham上同调.md` | https://stacks.math.columbia.edu/chapter/07GI | 404 | https://stacks.math.columbia.edu/chapter/07GI |
| `ref/Stacks-Tag-解读/Tag-0A99-模叠与模形式.md` | https://stacks.math.columbia.edu/chapter/0E6C | 404 | https://stacks.math.columbia.edu/chapter/0E6C |
| `ref/Stacks-Tag-解读/Tag-013Z-K-内射复形.md` | https://stacks.math.columbia.edu/tag/013Z | 404 | https://stacks.math.columbia.edu/tag/013Z |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/radon-nikodym-theorem.md` | https://terrytao.wordpress.com/2009/01/09/254a-notes-3a-measure-theory-lebesgue-measure/ | 404 | https://terrytao.wordpress.com/2009/01/09/254a-notes-3a-measure-theory-lebesgue-measure/ |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/dominated-convergence-theorem.md` | https://terrytao.wordpress.com/2009/01/11/the-dominated-convergence-theorem/ | 404 | https://terrytao.wordpress.com/2009/01/11/the-dominated-convergence-theorem/ |
| `FormalMath-Enhanced/02-Mathlib4-Annotations/Analysis/fubini-theorem.md` | https://terrytao.wordpress.com/2010/01/09/254a-notes-0a-an-alternate-approach-to-the-product-measure-extension-theorem/ | 404 | https://terrytao.wordpress.com/2010/01/09/254a-notes-0a-an-alternate-approach-to-the-product-measure-extension-theorem/ |
| `FormalMath-Interactive/docs/SEO-Implementation-Report.md` | https://twitter.com/formalmath | 404 | https://x.com/formalmath |
| `00-Stanford课程内容对齐报告.md` | https://web.stanford.edu/~jluk/math61CMautumn19/ | 404 | https://web.stanford.edu/~jluk/math61CMautumn19/ |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://www.d.umn.edu/\~jgallian/JavafixB.html | 404 | https://www.d.umn.edu/%5C~jgallian/JavafixB.html |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://www.d.umn.edu/\~jgallian/msproject06/project_xukai7 | 404 | https://www.d.umn.edu/%5C~jgallian/msproject06/project_xukai7 |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://www.d.umn.edu/\~jgallian/msproject06/project_xukai7.html | 404 | https://www.d.umn.edu/%5C~jgallian/msproject06/project_xukai7.html |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Contemporary Abstract Algebra 11ed 2025/full.md` | https://www.d.umn.edu/~jgallian/JavafixB.htmlm | 404 | https://www.d.umn.edu/~jgallian/JavafixB.htmlm |
| `project/ETH-Zurich-course-mapping.md` | https://www.ethz.ch/content/dam/ethz/special-interest/mavt/department-averoes/documents/Studium/Bachelor/Studienplan_BSc_MAVT_2023.pdf | 404 | https://ethz.ch/content/dam/ethz/special-interest/mavt/department-averoes/documents/Studium/Bachelor/Studienplan_BSc_MAVT_2023.pdf |
| `ref/Stacks-Tag-解读/Tag-03Q5-Etale上同调与正向极限交换.md` | https://www.jmilne.org/math/Books/EC.pdf | 404 | https://www.jmilne.org/math/Books/EC.pdf |
| `00-外部链接修复报告.md` | https://www.math.harvard.edu/course/mathematics-232br/；2025 | 404 | https://www.math.harvard.edu/course/mathematics-232br/%EF%BC%9B2025 |
| `project/00-权威源复核清单.md` | https://www.math.harvard.edu/course/mathematics-232br/；2025 | 404 | https://www.math.harvard.edu/course/mathematics-232br/%EF%BC%9B2025 |
| `00-海德堡大学数学课程对齐报告.md` | https://www.mathinf.uni-heidelberg.de/studies/ | 401 | https://www.mathinf.uni-heidelberg.de/studies/ |
| `00-外部链接修复报告.md` | https://www.maths.cam.ac.uk/postgrad/part-iii/courses | 404 | https://www.maths.cam.ac.uk/postgrad/part-iii/courses |
| `ref/Books/CategoryTheory/Conceptual Mathematics - A First Introduction To Categories/04-知识关联/04-权威机构与课程.md` | https://www.maths.cam.ac.uk/postgrad/part-iii/courses | 404 | https://www.maths.cam.ac.uk/postgrad/part-iii/courses |
| `ref/Books/CategoryTheory/Legatiuk D. Mathematical Modelling by Help of Category Theory...2025/04-知识关联/03-权威机构与课程.md` | https://www.maths.cam.ac.uk/postgrad/part-iii/courses | 404 | https://www.maths.cam.ac.uk/postgrad/part-iii/courses |
| `00-外部链接修复报告.md` | https://www.maths.cam.ac.uk/undergrad/nst/partia | 404 | https://www.maths.cam.ac.uk/undergrad/nst/partia |
| `ref/Books/AbstractAlgebra/Alcock L. How to Think About Abstract Algebra 2021/04-知识关联/04-权威机构与课程.md` | https://www.maths.cam.ac.uk/undergrad/nst/partia | 404 | https://www.maths.cam.ac.uk/undergrad/nst/partia |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/04-知识关联/04-权威机构与课程.md` | https://www.maths.cam.ac.uk/undergrad/nst/partia | 404 | https://www.maths.cam.ac.uk/undergrad/nst/partia |
| `ref/Books/AbstractAlgebra/Paulsen W. Abstract Algebra. An Interactive Approach 3ed 2025/04-知识关联/02-权威机构与课程.md` | https://www.maths.cam.ac.uk/undergrad/nst/partia | 404 | https://www.maths.cam.ac.uk/undergrad/nst/partia |
| `ref/Books/AbstractAlgebra/Gallian J. Contemporary Abstract Algebra 11ed 2025/Gallian J. Student Solutions Manual for Gallian's Cont. Abstr. Algebra 11ed 2025/full.md` | https://www.routledge.com/Textbooks-in-Mathematics/book-series/ | 404 | https://www.routledge.com/Textbooks-in-Mathematics/book-series/ |
| `00-东京大学数学课程对齐报告.md` | https://www.s.u-tokyo.ac.jp/ja/admission/undergraduate/pdf/ms2022.pdf | 404 | https://www.s.u-tokyo.ac.jp/ja/admission/undergraduate/pdf/ms2022.pdf |

## 四、不确定/瞬态链接清单（前 200 条）

| 文档路径 | 原链接 | 状态码 | 最终 URL |
|----------|--------|--------|----------|
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://cmap.ihmc.us/publications/ResearchPapers/ | 403 | https://cmap.ihmc.us/publications/ResearchPapers/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://cmap.ihmc.us/publications/ResearchPapers/ | 403 | https://cmap.ihmc.us/publications/ResearchPapers/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://cmc.ihmc.us | 500 | https://cmc.ihmc.us/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://cmc.ihmc.us | 500 | https://cmc.ihmc.us/ |
| `00-外部链接修复报告.md` | http://export.arxiv.org/api/ | 503 | https://export.arxiv.org/api/ |
| `docs/00-2025年arXiv数学前沿追踪-第1季度.md` | http://export.arxiv.org/api/ | 503 | https://export.arxiv.org/api/ |
| `00-全局导航与快速参考.md` | http://mizar.org/ | 500 | http://mizar.org/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://orgs.man.ac.uk/projects/include/experiment/communities.htm | 500 | http://orgs.man.ac.uk/projects/include/experiment/communities.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://orgs.man.ac.uk/projects/include/experiment/communities.htm | 500 | http://orgs.man.ac.uk/projects/include/experiment/communities.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm | 500 | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm | 500 | http://platea.pntic.mec.es/aperez4/miguel/Miguel%20de%20Guzm%E1n.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://standards.nctm.org/document/chapter3/index.htm | 500 | http://standards.nctm.org/document/chapter3/index.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://standards.nctm.org/document/chapter3/index.htm | 500 | http://standards.nctm.org/document/chapter3/index.htm |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.aamt.edu.au/standards | 403 | https://www.aamt.edu.au/standards |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.aamt.edu.au/standards | 403 | https://www.aamt.edu.au/standards |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.aamt.edu.au/standards/standxtm.pdf | 403 | https://www.aamt.edu.au/standards/standxtm.pdf |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.aamt.edu.au/standards/standxtm.pdf | 403 | https://www.aamt.edu.au/standards/standxtm.pdf |
| `ref/Books/AbstractAlgebra/Alcock L. How to Think About Abstract Algebra 2021/full.md` | http://www.ams.org/ | 403 | http://www.ams.org/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.emis.de/proceedings/PME29/PME29RRPapers/PME29Vol3Hansson.pdf | 403 | https://zbmath.org/emis/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.emis.de/proceedings/PME29/PME29RRPapers/PME29Vol3Hansson.pdf | 403 | https://zbmath.org/emis/ |
| `数学家理念体系/德利涅数学理念/02-数学内容深度分析/03-motives与Grothendieck纲领.md` | http://www.grothendieck-circle.org/ | 500 | http://www.grothendieck-circle.org/ |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.swinburne.edu.au/lss/statistics/IASE/CD | _ssl.c:1015: The handshake operation timed out | http://www.swinburne.edu.au/lss/statistics/IASE/CD |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.swinburne.edu.au/lss/statistics/IASE/CD | _ssl.c:1015: The handshake operation timed out | http://www.swinburne.edu.au/lss/statistics/IASE/CD |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics-Research-into-Practise-2008/full.md` | http://www.unix.oit.umass.edu/~afeldman/ActionResearchPapers/Feldman1996.PDF | 500 | http://www.unix.oit.umass.edu/~afeldman/ActionResearchPapers/Feldman1996.PDF |
| `ref/Books/Concept Mapping in Mathematics/Concept Mapping in Mathematics_ Research into Practice (2009, Springer US)/full.md` | http://www.unix.oit.umass.edu/~afeldman/ActionResearchPapers/Feldman1996.PDF | 500 | http://www.unix.oit.umass.edu/~afeldman/ActionResearchPapers/Feldman1996.PDF |
| `FormalMath-Enhanced/QUICKSTART.md` | http://your-domain.com:3000 | 500 | http://your-domain.com:3000 |
| `FormalMath-Enhanced/QUICKSTART.md` | http://your-domain.com:9090 | 500 | http://your-domain.com:9090 |
| `deploy/PRODUCTION_CHECKLIST.md` | https://alerts.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://alerts.formalmath.org |
| `tests/performance/README.md` | https://api-staging.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api-staging.formalmath.org |
| `FormalMath-Interactive/00-用户体验优化报告.md` | https://api.example.com | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.example.com |
| `FormalMath-Enhanced/api/app/docs/feedback_workflow.md` | https://api.example.com/api/v1/feedback/dashboard/summary | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.example.com/api/v1/feedback/dashboard/summary |
| `FormalMath-Enhanced/api/app/docs/feedback_workflow.md` | https://api.example.com/api/v1/feedback/feedbacks | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.example.com/api/v1/feedback/feedbacks |
| `FormalMath-Enhanced/api/app/docs/feedback_workflow.md` | https://api.example.com/api/v1/feedback/feedbacks/123 | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.example.com/api/v1/feedback/feedbacks/123 |
| `FormalMath-Enhanced/api/app/docs/feedback_workflow.md` | https://api.example.com/api/v1/feedback/feedbacks/123/responses | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.example.com/api/v1/feedback/feedbacks/123/responses |
| `FormalMath-Enhanced/api/app/docs/feedback_workflow.md` | https://api.example.com/api/v1/feedback/statistics | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.example.com/api/v1/feedback/statistics |
| `FormalMath-Enhanced/api/app/docs/feedback_workflow.md` | https://api.example.com/api/v1/feedback/trends | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.example.com/api/v1/feedback/trends |
| `tests/QUICKSTART.md` | https://api.example.com/data | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.example.com/data |
| `FormalMath-Enhanced/api/security/SECURITY_GUIDE.md` | https://api.formalmath.example.com/health | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.formalmath.example.com/health |
| `FormalMath-Enhanced/deployment/cdn/QUICKSTART.md` | https://api.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.formalmath.org |
| `tests/performance/README.md` | https://api.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.formalmath.org |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https://api.formalmath.org/api/v1 | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.formalmath.org/api/v1 |
| `docs/开发文档/03-前端开发指南.md` | https://api.formalmath.org/api/v1 | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.formalmath.org/api/v1 |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https://api.formalmath.org/api/v1/concepts | _ssl.c:1015: The handshake operation timed out | https://api.formalmath.org/api/v1/concepts |
| `FormalMath-Enhanced/deployment/cdn/QUICKSTART.md` | https://api.formalmath.org/api/v1/concepts | _ssl.c:1015: The handshake operation timed out | https://api.formalmath.org/api/v1/concepts |
| `FormalMath-Enhanced/deployment/cdn/README.md` | https://api.formalmath.org/api/v1/concepts | _ssl.c:1015: The handshake operation timed out | https://api.formalmath.org/api/v1/concepts |
| `00-上线检查清单与应急方案.md` | https://api.formalmath.org/health | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.formalmath.org/health |
| `FormalMath-Enhanced/05-AI-Formalization/01-KELPS.md` | https://api.kelps.example.com/v1 | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.kelps.example.com/v1 |
| `FormalMath-Enhanced/05-AI-Formalization/03-LeanAgent.md` | https://api.leanagent.example.com/v1 | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://api.leanagent.example.com/v1 |
| `00-应急方案详细手册.md` | https://apm.formalmath.internal | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://apm.formalmath.internal |
| `FormalMath-Enhanced/api/API_RELIABILITY_REPORT.md` | https://app.formalmath.com | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://app.formalmath.com |
| `FormalMath-Enhanced/api/security/SECURITY_GUIDE.md` | https://app.formalmath.example.com | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://app.formalmath.example.com |
| `FormalMath-Enhanced/api/security/SECURITY_HARDENING_REPORT.md` | https://app.formalmath.example.com | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://app.formalmath.example.com |
| `00-安全最终审计报告.md` | https://app.formalmath.io | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://app.formalmath.io |
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
| `00-外部链接修复报告.md` | https://arxiv.org/list/math.AT/recent | The read operation timed out | https://arxiv.org/list/math.AT/recent |
| `docs/11-高级数学/37-同伦论与代数拓扑前沿.md` | https://arxiv.org/list/math.AT/recent | The read operation timed out | https://arxiv.org/list/math.AT/recent |
| `project/00-项目全面批判性评价与改进计划-2025年11月30日.md` | https://blog.sina.com.cn/s/blog_635affba0100gfvp.html | 418 | https://blog.sina.com.cn/s/blog_635affba0100gfvp.html |
| `FormalMath-Enhanced/deployment/cdn/QUICKSTART.md` | https://cdn.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://cdn.formalmath.org |
| `docs/管理员手册/02-部署指南.md` | https://cdn.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://cdn.formalmath.org |
| `FormalMath-Enhanced/deployment/cdn/QUICKSTART.md` | https://cdn.formalmath.org/static/main.1234abcd.js | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://cdn.formalmath.org/static/main.1234abcd.js |
| `00-应急方案详细手册.md` | https://cdn.formalmath.org/static/main.js | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://cdn.formalmath.org/static/main.js |
| `ref/Books/00-ref-Books项目要求与权威对标全面梳理-2026年01月31日.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/00-权威对标与全面推进计划-2026年01月31日.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/Concept Mapping in Mathematics/01-历史发展/01-概念映射工具的发展与演变.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/Concept Mapping in Mathematics/06-思维表征方式/01-概念映射思维导图.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/Concept Mapping in Mathematics/07-最新研究进展/01-2024-2025最新研究综述.md` | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ | 403 | https://cmap.ihmc.us/publications/researchpapers/theorycmaps/ |
| `ref/Books/00-ref-Books项目要求与权威对标全面梳理-2026年01月31日.md` | https://ctl.stanford.edu/concept-mapping | <urlopen error _ssl.c:1015: The handshake operation timed out> | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/00-权威对标与全面推进计划-2026年01月31日.md` | https://ctl.stanford.edu/concept-mapping | <urlopen error _ssl.c:1015: The handshake operation timed out> | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/Concept Mapping in Mathematics/06-思维表征方式/01-概念映射思维导图.md` | https://ctl.stanford.edu/concept-mapping | <urlopen error _ssl.c:1015: The handshake operation timed out> | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/Concept Mapping in Mathematics/06-思维表征方式/02-概念映射多维矩阵.md` | https://ctl.stanford.edu/concept-mapping | <urlopen error _ssl.c:1015: The handshake operation timed out> | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/Concept Mapping in Mathematics/06-思维表征方式/03-概念映射应用决策树.md` | https://ctl.stanford.edu/concept-mapping | <urlopen error _ssl.c:1015: The handshake operation timed out> | https://ctl.stanford.edu/concept-mapping |
| `ref/Books/Concept Mapping in Mathematics/07-最新研究进展/01-2024-2025最新研究综述.md` | https://ctl.stanford.edu/concept-mapping | <urlopen error _ssl.c:1015: The handshake operation timed out> | https://ctl.stanford.edu/concept-mapping |
| `00-应急方案详细手册.md` | https://dash.cloudflare.com | 403 | https://dash.cloudflare.com |
| `FormalMath-Enhanced/06-Modern-Frontiers/SciML/mit-18.337j-notes.md` | https://diffeqflux.sciml.ai/ | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://diffeqflux.sciml.ai/ |
| `数学家理念体系/00-ONLINE-RESOURCES-ALIGNMENT.md` | https://dl.acm.org/ | 403 | https://dl.acm.org/ |
| `00-FormalMath项目质量白皮书.md` | https://docs.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://docs.formalmath.org |
| `00-外部链接修复报告.md` | https://docs.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://docs.formalmath.org |
| `docs/00-认知诊断系统使用指南.md` | https://docs.formalmath.org | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://docs.formalmath.org |
| `FormalMath-Enhanced/api/docs/API_GUIDE.md` | https://docs.formalmath.org/api | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://docs.formalmath.org/api |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1002/hbm.460020402 | 403 | https://onlinelibrary.wiley.com/doi/10.1002/hbm.460020402 |
| `docs/10-应用数学/01-核心内容/信息论-香农编码定理-深度扩展.md` | https://doi.org/10.1002/j.1538-7305.1948.tb01338.x | 418 | https://ieeexplore.ieee.org/document/6773024 |
| `concept/view/07-国际数学教育研究/03-新加坡数学教育/03-新加坡数学教育.md` | https://doi.org/10.1007/s10763-009-9173-4 | 404 | https://doi.org/10.1007/s10763-009-9173-4 |
| `00-外部链接修复报告.md` | https://doi.org/10.1016/S0079-7421(08) | 404 | https://doi.org/10.1016/S0079-7421(08) |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1080/02643290244000239 | 403 | https://www.tandfonline.com/doi/abs/10.1080/02643290244000239 |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1093/oxfordhb/9780199642342.013.041 | 403 | https://academic.oup.com/edited-volume/34494/chapter/292679312 |
| `concept/view/06-数学认知的计算模型/02-计算解剖学视角/02-计算解剖学视角.md` | https://doi.org/10.1207/s15516709cog0502_2 | 403 | https://onlinelibrary.wiley.com/doi/10.1207/s15516709cog0502_2 |
| `concept/view/07-国际数学教育研究/03-新加坡数学教育/03-新加坡数学教育.md` | https://doi.org/10.5951/jresematheduc.40.3.0282 | 403 | https://pubs.nctm.org/view/journals/jrme/40/3/article-p282.xml |
| `00-EPFL数学课程对齐报告.md` | https://edu.epfl.ch/coursebook | 403 | https://edu.epfl.ch/coursebook/ |
| `数学家理念体系/魏尔斯特拉斯数学理念/01-核心理论/05-数学写作与教育理念.md` | https://en.wikipedia.org/wiki/Berlin_School_of_Mathematics | 403 | https://en.wikipedia.org/wiki/Berlin_School_of_Mathematics |
| `concept/00-范畴论视角-核心概念分析/29-图-范畴论视角分析.md` | https://en.wikipedia.org/wiki/Category_of_graphs | 403 | https://en.wikipedia.org/wiki/Category_of_graphs |
| `数学家理念体系/布尔数学理念/01-核心理论/03-符号逻辑理论.md` | https://en.wikipedia.org/wiki/Formal_logic | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/Formal_logic |
| `数学家理念体系/00-归档-2026年4月-其他数学家/布劳威尔数学理念/01-核心理论/03-排中律批判与自由选择序列.md` | https://en.wikipedia.org/wiki/Free_choice_sequence | 403 | https://en.wikipedia.org/wiki/Free_choice_sequence |
| `数学家理念体系/布尔数学理念/00-文档索引.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/01-核心理论/01-数学哲学与方法论.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/01-核心理论/02-核心数学思想.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/01-核心理论/03-理论体系构建.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/01-核心理论/04-方法论贡献.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/01-核心理论/05-学术影响与传承.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/01-核心理论/05-数学写作与教育理念.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/02-数学内容深度分析/01-核心贡献领域一.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/02-数学内容深度分析/02-核心贡献领域二.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/02-数学内容深度分析/03-核心贡献领域三.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/02-数学内容深度分析/04-技术创新与方法.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |
| `数学家理念体系/布尔数学理念/03-教育与影响/01-教育理念与方法.md` | https://en.wikipedia.org/wiki/George_Boole | [SSL: UNEXPECTED_EOF_WHILE_READING] EOF occurred in violation of protocol (_ssl.c:1032) | https://en.wikipedia.org/wiki/George_Boole |

## 五、说明

- **确认失效**：`404`、不可解析主机、非瞬态 `4xx` 等，需要替换或删除。
- **不确定/瞬态**：`403/429` 频率限制、`5xx`、超时、SSL 握手异常等，建议人工复核或稍后重试。
- `301/302` 跳转后的目标若返回 `200`，视为可用。
- Wikidata 实体页因对批量 HEAD 敏感，已跳过校验。