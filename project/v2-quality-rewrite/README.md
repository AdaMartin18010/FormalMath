# FormalMath v2.0 质量重写总控中心

**项目代号**: `v2-quality-rewrite`  
**战略目标**: 从数量扩张转向质量深耕，将项目从目录级对齐升级为语义级对齐  
**启动日期**: 2026-04-04  
**总周期**: 18-24个月  
**状态**: 🟡 阶段一启动中

---

## 执行原则

1. **中断恢复**: 任何时候都可以停止，通过 `master-plan.yaml` 和 `context-snapshots/` 恢复上下文
2. **大规模并行**: 任务拆分为独立单元，通过子代理并行执行
3. **可验证交付**: 每个任务必须有明确的验收标准，输出到 `deliverables/`
4. **版本诚实**: 项目对外标记为 `v2.0-rewrite`，不再使用 `v1.0-final`

---

## 目录结构

```
project/v2-quality-rewrite/
├── README.md                    # 本文件 - 总控说明
├── master-plan.yaml             # 全局任务计划与状态跟踪
├── task-registry/               # 每个任务的注册信息
│   ├── T001-quality-rubric.md
│   ├── T002-alignment-checklist.md
│   └── ...
├── deliverables/                # 经过验收的交付物
│   ├── D001-quality-framework.md
│   ├── D002-course-syllabus-mit-18-100a.yaml
│   └── ...
├── context-snapshots/           # 定期保存的执行上下文
│   └── snapshot-YYYY-MM-DD-HHMMSS.yaml
├── workspaces/                  # 各任务工作区
│   ├── audit/                   # 质量审计相关
│   ├── courses/                 # 课程对齐相关
│   └── standards/               # 标准规范相关
└── scripts/                     # 自动化脚本（待创建）
    ├── task-status-check.ps1
    └── batch-spawn-tasks.ps1
```

---

## 快速状态

查看当前所有任务状态：
```powershell
Get-Content master-plan.yaml | Select-String "status:"
```

查看最新上下文快照：
```powershell
Get-ChildItem context-snapshots/ | Sort-Object LastWriteTime -Descending | Select-Object -First 1
```

---

## 子代理任务规范

每个子代理（Task）必须：

1. **读取 `master-plan.yaml` 中自己任务的上下文**
2. **输出到 `workspaces/{领域}/T{编号}-{任务名}/`**
3. **生成 `task-report.md`**，包含：
   - 执行摘要
   - 输出文件清单
   - 遇到的问题或阻塞
   - 建议的下游任务
4. **完成任务后更新 `master-plan.yaml` 中的状态**（由总控代理执行）

---

## 当前进行中的任务批次

### 第一批：基础设施与课程拆解（Batch-01）
- `T001` 质量审计评分标准设计
- `T002` L3-L6语义对齐验证手册
- `T003` 参考文献硬链接规范
- `T004` 双语（自然语言+Lean4）文档模板
- `T005` 三层内容金字塔写作标准v2.0
- `T006` MIT 18.100A 课程大纲完整拆解
- `T007` MIT 18.701 课程大纲完整拆解
- `T008` MIT 18.06/18.700 线性代数课程大纲完整拆解
- `T009` Harvard Math 232br 课程大纲完整拆解
- `T010` Stanford FOAG 课程大纲完整拆解

---

*最后更新: 2026-04-04*
