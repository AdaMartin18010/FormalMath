---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# API文档索引
**生成时间**: 2026-04-04 13:07:41
**总API数**: 759

## 模块列表
### api.py
**类**:
- `APIResponse` - API响应封装...
- `UserProfileAPI` - 用户画像API...
- `RecommendationAPI` - 推荐API...
- `VisualizationAPI` - 可视化API...

**函数**:
- `initialize_default_engine()`

### api_doc_generator.py
**类**:
- `APIMember` - API成员信息...
- `APIDocGenerator` - API文档生成器

自动解析Python源代码，提取类和函数的文档，生成结构化的API文档...

**函数**:
- `main()`

### assessment_system.py
**类**:
- `AssessmentConfig` - 评估配置...
- `AssessmentSession` - 评估会话...
- `AssessmentResult` - 评估结果...
- `FormalMathAssessmentSystem` - FormalMath 评估系统核心类

整合所有评估功能，提供统一的评估接口

Attributes...

### calculate_rewards.py
**类**:
- `RewardResult` - 奖励计算结果...
- `RewardCalculator` - 积分计算器...

**函数**:
- `main()`

### check_links.py
**类**:
- `LinkCheckResult` - 链接检查结果...
- `LinkChecker` - 链接检查器...

**函数**:
- `main()`

### ci_content_check.py
**类**:
- `Issue` - 检查发现问题...
- `CIContentChecker` - CI 内容检查器...

**函数**:
- `main()`

### concept_graph_generator.py
**类**:
- `Concept` - 概念节点...
- `ConceptRelation` - 概念关系...
- `ConceptGraphGenerator` - 概念图谱生成器

从Markdown文档中提取概念信息，生成知识图谱、可视化数据和文档...

**函数**:
- `main()`

### config.py
**类**:
- `AssessmentConfig` - 评估配置类...

**函数**:
- `get_config() -> AssessmentConfig`
- `update_weights(new_weights)`
- `add_math_terms(terms)`
- `set_quality_thresholds(thresholds)`

### demo.py
**函数**:
- `print_separator(title: str = )`
- `print_subsection(title: str)`
- `demo_basic_evaluation()`
- `demo_scoring_engine()`
- `demo_feedback_generation()`
- `demo_full_assessment_system()`
- `demo_performance_assessment()`
- `demo_divergent_assessment()`
- `demo_realtime_feedback()`
- `demo_diagnosis_integration()`
- `main()`

### demo_demo.py
**函数**:
- `print_section(title)`
- `demo_single_file_assessment()`
- `demo_batch_assessment()`
- `demo_report_generation(results, summary)`
- `demo_issue_extraction(results)`
- `main()`

### diagnosis_engine.py
**类**:
- `ResponseType` - 答题响应类型...
- `Response` - 答题响应...
- `KnowledgeState` - 知识状态...
- `Suggestion` - 学习建议...
- `DiagnosisResult` - 诊断结果...
- `HCDAlgorithm` - HCD (Hierarchical Cognitive Diagnosis) 算法

基于层次约束感...
- `DiagnosisEngine` - 诊断引擎主类...

### doc_generator.py
**类**:
- `GenerationConfig` - 文档生成配置...
- `DocumentGenerator` - FormalMath 统一文档生成器

整合所有文档生成功能，提供统一的生成接口...

**函数**:
- `main()`

### evaluation_criteria.py
**类**:
- `AssessmentType` - 评估类型枚举...
- `EvaluationLevel` - 评价等级枚举...
- `DimensionWeight` - 维度权重定义...
- `ConceptualUnderstanding` - 概念理解 (Conceptual Understanding)

评估学习者对数学概念、原理、关系的...
- `ProceduralFluency` - 程序流畅性 (Procedural Fluency)

评估学习者执行数学程序的灵活、准确、高效程度...
- `StrategicCompetence` - 策略能力 (Strategic Competence)

评估学习者制定和运用数学策略解决问题的能力...
- `AdaptiveReasoning` - 适应性推理 (Adaptive Reasoning)

评估学习者进行逻辑思考、解释、论证的能力...
- `ProductiveDisposition` - 数学产出 (Productive Disposition)

评估学习者将数学视为有意义、有价值、可...
- `LearningParticipation` - 学习参与度指标...
- `LearningInitiative` - 学习主动性指标...
- `LearningProgress` - 学习进度指标...
- `ValueAddedMetrics` - 增值评价指标...
- `OperationalAbility` - 操作能力指标...
- `CreativeProduct` - 创造产品指标...
- `CreativityMetrics` - 创造性指标...
- `MathematicalAbilityProfile` - 数学能力档案

整合五维数学能力指标的完整档案...
- `EvaluationCriteria` - 评价标准定义

定义各评价等级的分数阈值...
- `LearnerProfile` - 学习者档案...

### extend_concepts.py
**函数**:
- `load_existing_concepts(filepath)`
- `create_new_concepts()`
- `main()`

### feedback_generator.py
**类**:
- `FeedbackType` - 反馈类型枚举...
- `FeedbackPriority` - 反馈优先级...
- `FeedbackItem` - 反馈项...
- `FeedbackReport` - 反馈报告...
- `FeedbackTemplates` - 反馈模板库...
- `LearningSuggestions` - 学习建议库...
- `FeedbackGenerator` - 反馈生成器

根据评估结果生成个性化反馈和学习建议...
- `RealTimeFeedbackGenerator` - 实时反馈生成器

在学习过程中提供即时反馈...

### generate_docs.py
**函数**:
- `create_parser()`
- `main()`

### generate_extended_concepts.py
**函数**:
- `generate_statistics(all_concepts)`
- `main()`

### generate_quality_report.py
**类**:
- `QualityReportGenerator` - 质量报告生成器...

**函数**:
- `main()`

### generate_visualization_data.py
**函数**:
- `parse_concepts(yaml_file)`
- `generate_visualization_data(concepts, metadata)`
- `get_category_group(category)`
- `generate_mermaid_diagram(concepts, max_nodes = 50)`
- `generate_statistics_report(concepts, metadata)`
- `main()`

### i18n_generator.py
**类**:
- `TranslationEntry` - 翻译条目...
- `I18nGenerator` - 国际化文档生成器

生成多语言版本的文档，支持中英文对照...

**函数**:
- `main()`

### issue_extractor.py
**类**:
- `IssueItem` - 问题项...
- `IssueCategory` - 问题分类...
- `IssueExtractor` - 问题提取器...
- `BatchIssueProcessor` - 批量问题处理器...

**函数**:
- `main()`

### lean4_doc_generator.py
**类**:
- `LeanTheorem` - Lean定理信息...
- `LeanDefinition` - Lean定义信息...
- `Lean4DocGenerator` - Lean4文档生成器

解析Lean4源码文件(.lean)，提取定理、定义、证明结构，
生成格式化...

**函数**:
- `main()`

### main.py
**函数**:
- `print_banner()`
- `cmd_assess(args)`
- `cmd_extract(args)`
- `cmd_config(args)`
- `main()`
- `print_header(text: str)`
- `print_section(text: str)`
- `demo_full_workflow()`
- `run_api_server(host: str = 127.0.0.1, port: int = 8000)`
- `run_tests()`
- `main()`

### merge_concepts.py
**函数**:
- `load_file(filepath)`
- `merge_concepts()`

### metadata_cli.py
**类**:
- `MetadataManager` - 元数据管理器...

**函数**:
- `main()`

### metadata_extractor.py
**类**:
- `MetadataRecord` - 元数据记录类...
- `MetadataExtractor` - 元数据提取器...

**函数**:
- `main()`

### metadata_query.py
**类**:
- `QueryResult` - 查询结果...
- `MetadataQuery` - 元数据查询系统...

**函数**:
- `interactive_query()`

### msc_alignment_final.py
**函数**:
- `extract_frontmatter(content: str)`
- `get_msc_info(frontmatter)`
- `scan_concepts()`
- `validate_msc_code(code: str)`
- `check_classification_accuracy(concepts) -> Dict`
- `generate_correction_plan(check_results: Dict)`
- `create_msc_reverse_index(concepts) -> Dict`
- `generate_hierarchy_data(reverse_index: Dict) -> Dict`
- `generate_report(concepts, check_results: Dict, corrections, reverse_index: Dict, hierarchy: Dict) -> str`
- `main()`

### msc_annotation_phase2.py
**函数**:
- `has_msc(content)`
- `detect_msc_from_filename(filename, content)`
- `add_msc_to_frontmatter(content, primary, secondary)`
- `process_file(filepath)`
- `main()`

### msc_annotation_sprint.py
**函数**:
- `detect_msc_from_content(filepath, content, branch)`
- `has_frontmatter(content)`
- `has_msc(content)`
- `add_msc_to_frontmatter(content, primary, secondary)`
- `process_file(filepath, branch)`
- `main()`

### msc_batch_processor.py
**函数**:
- `has_msc_encoding(file_path)`
- `determine_msc_code(file_path, relative_path)`
- `add_msc_to_file(file_path, msc_code)`
- `scan_and_process(base_dir)`
- `print_report(stats)`

### msc_final_report.py
**函数**:
- `has_msc_encoding(file_path)`
- `get_directory_category(relative_path)`
- `scan_and_report(base_dir)`
- `print_report(stats)`

### path_visualization.py
**类**:
- `VisualizationTheme` - 可视化主题...
- `TimelineEvent` - 时间线事件...
- `TimelineView` - 时间线视图...
- `PathGraphView` - 路径依赖图视图...
- `ProgressTracker` - 进度追踪器...
- `DashboardRenderer` - 仪表板渲染器...

**函数**:
- `export_path_to_json(path: LearningPath, user_profile: UserProfile)`

### pre_commit_check.py
**类**:
- `CheckResult` - 检查结果...
- `PreCommitChecker` - 预提交检查器...

**函数**:
- `get_staged_files()`
- `main()`

### quality_assessor.py
**类**:
- `QualityLevel` - 质量等级...
- `CompletenessMetrics` - 完整性指标...
- `AccuracyMetrics` - 准确性指标...
- `ReadabilityMetrics` - 可读性指标...
- `InternationalizationMetrics` - 国际化指标...
- `LearningEffectMetrics` - 学习效果预测指标...
- `QualityAssessmentResult` - 质量评估结果...
- `ContentQualityAssessor` - 内容质量评估器...

**函数**:
- `main()`

### quality_control.py
**类**:
- `QualityLevel` - 质量等级...
- `QualityReport` - 质量报告...
- `QualityControl` - 质量控制器...

**函数**:
- `main()`

### recommendation_engine.py
**类**:
- `PathStrategy` - 路径生成策略...
- `PathNode` - 路径节点...
- `LearningPath` - 学习路径...
- `ConceptGraph` - 概念依赖图 - 基于NetworkX的包装器...
- `PathScorer` - 路径评分器...
- `RecommendationEngine` - 个性化学习路径推荐引擎...

**函数**:
- `create_sample_graph() -> ConceptGraph`

### report_generator.py
**类**:
- `ReportType` - 报告类型枚举...
- `ReportFormat` - 报告格式枚举...
- `ReportSection` - 报告章节...
- `AssessmentReport` - 评估报告基类...
- `BaseReportGenerator` - 报告生成器基类...
- `ProgressReportGenerator` - 学习进度报告生成器...
- `AbilityReportGenerator` - 能力评估报告生成器...
- `ValueAddedReportGenerator` - 增值评价报告生成器...
- `ReportExporter` - 报告导出器...
- `ReportGenerator` - 报告生成器主类

整合所有报告生成功能，提供统一的报告生成接口...
- `ReportGenerator` - 报告生成器...

**函数**:
- `main()`

### scoring_engine.py
**类**:
- `ScoringAlgorithm` - 评分算法基类...
- `WeightedScoringModel` - 加权评分模型

支持多维度加权评分，可配置不同维度和指标的权重...
- `ValueAddedScoringModel` - 增值评分模型

评估学习者在一定时期内的能力提升和价值增值...
- `PerformanceScoringModel` - 表现性评分模型

评估学习者在真实任务情境中的表现...
- `DivergentThinkingScoringModel` - 发散思维评分模型

评估学习者的创造性思维能力...
- `ProcessScoringModel` - 过程性评分模型

评估学习过程中的参与度和行为...
- `ScoringEngine` - 评分引擎主类

整合所有评分模型，提供统一的评分接口...

### update_leaderboard.py
**类**:
- `LeaderboardGenerator` - 排行榜生成器...

**函数**:
- `main()`

### user_profile.py
**类**:
- `LearningStyle` - 学习风格类型 - 基于Felder-Silverman学习风格模型简化版...
- `ProficiencyLevel` - 熟练度等级...
- `LearningGoalPriority` - 学习目标优先级...
- `ConceptMastery` - 概念掌握度记录...
- `LearningPreference` - 学习偏好设置...
- `TimePreference` - 时间偏好设置...
- `LearningGoal` - 学习目标定义...
- `LearningHistory` - 学习历史记录...
- `UserProfile` - 用户画像 - 个性化学习路径推荐的核心数据结构

包含用户的学习特征、目标、偏好和历史记录...

**函数**:
- `create_preset_profile(preset_type: str, name: str = , email: str = ) -> UserProfile`

### validate_msc.py
**类**:
- `MSCValidationResult` - MSC 验证结果...
- `MSCValidator` - MSC 编码验证器...

**函数**:
- `main()`

### version_control.py
**类**:
- `VersionInfo` - 版本信息...
- `ChangeRecord` - 变更记录...
- `VersionControl` - 文档版本控制系统...
- `MetadataVersionManager` - 元数据版本管理器...

**函数**:
- `main()`

### wikipedia_complete_align.py
**函数**:
- `load_concepts(yaml_path: str)`
- `generate_multilang_table(concepts)`
- `generate_json_output(table, output_path: str)`
- `generate_markdown_report(table, output_path: str)`
- `update_yaml_with_multilang(yaml_path: str, table, output_path: str)`
- `main()`

### wikipedia_fast_align.py
**函数**:
- `load_concepts(yaml_path: str)`
- `generate_multilang_table(concepts)`
- `generate_json_output(table, output_path: str)`
- `generate_markdown_report(table, output_path: str)`
- `update_yaml_with_multilang(yaml_path: str, table, output_path: str)`
- `main()`

### wikipedia_final_align.py
**函数**:
- `load_concepts(yaml_path: str)`
- `generate_multilang_table(concepts)`
- `generate_json_output(table, output_path: str)`
- `generate_markdown_report(table, output_path: str)`
- `update_yaml_with_multilang(yaml_path: str, table, output_path: str)`
- `main()`

### wikipedia_multilang_align.py
**类**:
- `MultilangInfo` - 多语言信息...
- `WikipediaMultilangAligner` - Wikipedia多语言对齐器...

### wikipedia_multilang_demo.py
**类**:
- `MultilangInfo` - 多语言信息...
- `DemoAligner` - 演示版本对齐器...

### 批量修正符号.py
**函数**:
- `should_exclude(filepath)`
- `fix_symbols_in_file(filepath, backup = True)`
- `main()`

