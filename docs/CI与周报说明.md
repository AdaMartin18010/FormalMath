# CI 门禁与周报生成说明

## 触发

- PR：仅检查改动文件 + 受影响索引
- main 每周五 18:00：全量检查与周报生成

## 命令

```bash
python tools/check_quality.py --scope docs --rules terminology,symbols --report out/report-$(date +%Y%m%d).json
```

## 阈值

- 质量分 < 0.95 或 issues ≥ 10：失败并阻止合并

## 周报产物

- out/report-YYYYMMDD.json / out/report-YYYYMMDD.md
- out/coverage-matrix.csv（对标覆盖率）
- out/bad-links.csv（坏链）
- out/term-aliases.csv（别称命中）

## 失败处理

- PR 自动评论列出前 20 条问题与修复建议
- 紧急豁免：添加标签 `override: allowed`，需在一周内补齐
