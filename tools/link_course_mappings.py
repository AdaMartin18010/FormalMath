#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为 project/ 下的国际课程对齐文档自动添加指向 docs/ 内容的超链接。
"""

import argparse
import re
import sys
from pathlib import Path
from typing import List, Tuple, Set

# 匹配规则: (关键词列表, 链接显示文本, 链接目标)
LINK_RULES: List[Tuple[List[str], str, str]] = [
    # 分析学
    (["Real Analysis", "实分析", "数学分析", "Mathematical Analysis"], "实分析", "../docs/03-分析学/"),
    (["Calculus", "微积分", "Multivariable Calculus"], "微积分", "../docs/03-分析学/"),
    (["Complex Analysis", "复分析", "复变函数"], "复分析", "../docs/03-分析学/"),
    (["Functional Analysis", "泛函分析"], "泛函分析", "../docs/03-分析学/"),
    (["Measure Theory", "测度论"], "测度论", "../docs/03-分析学/"),
    (["Differential Equations", "微分方程"], "微分方程", "../docs/05-微分方程/"),
    (["Numerical Analysis", "数值分析"], "数值分析", "../docs/07-数值分析/"),
    (["Fourier Analysis", "Fourier分析"], "Fourier分析", "../docs/03-分析学/"),
    (["Harmonic Analysis", "调和分析"], "调和分析", "../docs/03-分析学/"),
    (["Convex Optimization", "凸优化"], "凸优化", "../docs/21-最优化/"),
    (["ODE", "常微分方程"], "常微分方程", "../docs/05-微分方程/"),
    (["PDE", "偏微分方程"], "偏微分方程", "../docs/05-微分方程/"),

    # 代数
    (["Linear Algebra", "线性代数"], "线性代数", "../docs/02-代数结构/"),
    (["Abstract Algebra", "抽象代数", "代数学", "Algebra I", "Algebra II", "Graduate Algebra"], "抽象代数", "../docs/02-代数结构/"),
    (["Commutative Algebra", "交换代数"], "交换代数", "../docs/02-代数结构/"),
    (["Group Theory", "群论", "Groups and Group Actions"], "群论", "../docs/02-代数结构/"),
    (["Ring Theory", "环论", "Rings and Modules"], "环论", "../docs/02-代数结构/"),
    (["Field Theory", "域论", "Galois Theory"], "域论", "../docs/02-代数结构/"),
    (["Lie Algebras", "李代数"], "李代数", "../docs/02-代数结构/"),
    (["Homological Algebra", "同调代数"], "同调代数", "../docs/15-同调代数/"),
    (["Representation Theory", "表示论"], "表示论", "../docs/02-代数结构/"),
    (["Module Theory", "模论"], "模论", "../docs/02-代数结构/"),
    (["Universal Algebra", "泛代数"], "泛代数", "../docs/02-代数结构/"),

    # 几何与拓扑
    (["Algebraic Topology", "代数拓扑"], "代数拓扑", "../docs/12-代数拓扑/"),
    (["Algebraic Geometry", "代数几何"], "代数几何", "../docs/13-代数几何/"),
    (["Differential Geometry", "微分几何", "Differential Manifolds"], "微分几何", "../docs/04-几何与拓扑/"),
    (["Riemannian Geometry", "黎曼几何"], "黎曼几何", "../docs/04-几何与拓扑/"),
    (["Topology", "拓扑学", "Metric and Topological Spaces"], "拓扑学", "../docs/04-几何与拓扑/"),
    (["Geometry", "几何"], "几何", "../docs/04-几何与拓扑/"),

    # 数论
    (["Algebraic Number Theory", "代数数论"], "代数数论", "../docs/05-数论/"),
    (["Analytic Number Theory", "解析数论"], "解析数论", "../docs/05-数论/"),
    (["Number Theory", "数论"], "数论", "../docs/05-数论/"),

    # 概率统计
    (["Probability and Statistics", "概率论与统计"], "概率论与统计", "../docs/06-概率论与统计/"),
    (["Probability", "概率论", "随机过程", "Stochastic Processes"], "概率论", "../docs/06-概率论与统计/"),
    (["Statistics", "统计学", "数理统计"], "统计学", "../docs/06-概率论与统计/"),

    # 逻辑与基础
    (["Mathematical Logic", "数理逻辑"], "数理逻辑", "../docs/07-数理逻辑/"),
    (["Set Theory and Logic", "集合论与逻辑"], "集合论与逻辑", "../docs/07-数理逻辑/"),
    (["Logic", "逻辑学", "命题逻辑", "一阶逻辑", "证明理论"], "数理逻辑", "../docs/07-数理逻辑/"),
    (["Set Theory", "集合论", "ZFC"], "集合论", "../docs/01-基础数学/"),

    # 离散与组合
    (["Combinatorics", "组合数学", "Graph Theory", "图论", "Extremal Combinatorics"], "组合数学", "../docs/09-组合数学与离散数学/"),
    (["Discrete Mathematics", "离散数学"], "离散数学", "../docs/09-组合数学与离散数学/"),

    # 计算与形式化
    (["Computational Mathematics", "计算数学"], "计算数学", "../docs/08-计算数学/"),
    (["Formal Proof", "形式化证明", "Lean4", "Coq"], "形式化证明", "../docs/09-形式化证明/"),

    # 应用与其他
    (["Cryptography", "密码学"], "密码学", "../docs/24-密码学/"),
    (["Optimization", "最优化", "运筹学", "Operations Research"], "最优化", "../docs/21-最优化/"),
    (["Game Theory", "博弈论"], "博弈论", "../docs/21-最优化/"),
    (["Machine Learning", "机器学习"], "机器学习", "../docs/29-数据科学/"),
    (["Data Science", "数据科学"], "数据科学", "../docs/29-数据科学/"),
    (["Control Theory", "控制论"], "控制论", "../docs/22-控制论/"),
    (["Information Theory", "信息论"], "信息论", "../docs/23-信息论/"),
    (["Financial Mathematics", "金融数学"], "金融数学", "../docs/25-金融数学/"),
    (["Mathematical Physics", "数学物理"], "数学物理", "../docs/11-数学物理/"),
    (["Category Theory", "范畴论"], "范畴论", "../docs/01-基础数学/"),
    (["Dynamical Systems", "动力系统"], "动力系统", "../docs/10-应用数学/"),
]


# 过于通用的中文字词，过滤掉以避免统计噪音
COMMON_CHINESE_WORDS = set(
    "定理 定义 证明 性质 应用 理论 基础 空间 函数 映射 运算 结构 方法 概念 例子 练习 笔记 讲义 教材 课程 内容 章节 模块 专题 引言 结论 摘要 介绍 概述 总结 分析 讨论 研究 学习 教学 考试 作业 项目 报告 论文 文献 参考 资源 链接 页面 网站 版本 更新 维护 状态 进度 计划 安排 时间 日期 学期 学年 年级 学分 学时 小时 分钟 程度 水平 标准 规范 规则 要求 条件 限制 约束 假设 前提 结果 答案 解答 解析 说明 注释 备注 提示 警告 注意 重要 关键 核心 主要 基本 初步 深入 高级 进阶 入门 初学 提高 强化 扩展 补充 完善 优化 改进 修正 修订 编辑 编写 创作 设计 开发 实现 构建 建立 创建 生成 产生 导出 导入 输入 输出 读取 写入 保存 加载 显示 隐藏 展开 折叠 排序 筛选 搜索 查找 替换 删除 插入 添加 移除 移动 复制 粘贴 剪切 撤销 恢复 重做 清空 重置 默认 初始 最终 最后 首先 第一 第二 第三 第四 第五 第六 第七 第八 第九 第十 之一 之二 之三 部分 全部 整体 局部 细节 大局 方面 角度 层次 维度 领域 范围 范畴 类型 种类 形式 方式 模式 模型 实例 案例 示例 范例 样本 模板 框架 体系 系统 平台 工具 技术 技能 能力 知识 经验 背景 历史 发展 现状 趋势 未来 前景 目标 目的 意义 价值 作用 影响 效果 成果 效益 收益 产出 贡献 成就 成绩 表现 评价 评估 测量 测定 计算 统计 计数 数量 数值 数字 数据 信息 消息 信号 符号 标记 标识 标志 标签 名称 标题 题目 主题 话题 问题 疑问 难题 挑战 困难 障碍 错误 失误 缺陷 漏洞 风险 危险 安全 保障 保护 维护 修复 解决 处理 应对 适应 调整 改变 变化 变动 差异 区别 区分 分辨 识别 认识 了解 理解 掌握 熟悉 精通 擅长 善于 能够 可以 可能 也许 大概 大约 约莫 几乎 差不多 根本 完全 绝对 相对 比较 较为 非常 十分 特别 尤其 格外 相当 很 太 极 最 更 较 稍 略 对比 对照 对应 匹配 适合 合适 恰当 适当 正好 恰好 刚好 碰巧 偶然 必然 当然 自然 显然 明显 清楚 清晰 明确 确定 肯定 一定 必须 必要 需要 需求 请求 申请 申报 报告 汇报 通知 通告 公告 公布 发布 发表 声明 宣布 传达 传播 传递 传输 交换 交流 沟通 协商 协调 合作 协作 配合 支持 帮助 协助 辅助 指导 引导 领导 带领 率领 主持 负责 管理 治理 统治 控制 支配 掌握 把握 抓住 抓紧 保持 保守 守旧 陈旧 老旧 古老 老套 俗套 套路 道路 路途 路程 途径 渠道 门路 路子 路线 轨道 轨迹 痕迹 印记 印象 影响 后果 效用 机能 机制 体制 制度 规矩 规程 法则 原则 原理 定律 规律 法律 法规 条例 规章 章程 大纲 纲要 要领 要点 重点 难点 疑点 基点 支点 据点 基地 根基 根底 底子 底细 详情 细微 细小 微小 渺小 轻微 微弱 薄弱 脆弱 软弱 虚弱 衰弱 衰退 衰落 衰败 败落 落魄 潦倒 困顿 艰难 艰苦 艰辛 辛苦 辛劳 勤劳 勤奋 勤勉 刻苦 努力 奋力 竭力 尽力 倾力 专心 专注 专一 专门 专业 职业 事业 产业 行业 行当 行话 术语 名词 词汇 词语 单词 单字 字母 字符 文字 字体 字形 字型 书法 写法 读法 念法 说法 讲法 看法 想法 做法 办法 形态 状态 情况 情形 情景 场景 场面 场合 场所 场地 地方 地区 区域 区划 划分 分割 分裂 分离 分开 分散 分布 散布 通行 通用 公用 公共 共同 共有 共享 分担 分摊 分配 配置 安置 安排 部署 布置 设置 设立 创设 促进 促使 导致 引起 引发 造成 形成 构成 组成 包含 包括 涵盖 涉及 关系到 关于 有关 相关 联系 关联 连接 衔接 结合 融合 整合 综合 统一 一致 相同 相似 类似 相近 接近 靠近 邻近 附近 周围 周边 边缘 边界 界限 界线 极限 极端 顶端 底部 上层 下层 高层 底层 内部 外部 表面 里面 外面 中间 中央 中心 出发点 落脚点 归宿 终点 起点 原点 因为 所以 因此 因而 于是 从而 进而 反而 相反 相比 较之 比起 对照 反差 差距 差别 不同 分别 各自 单独 独立 自主 自动 自觉 自愿 自发 忽然 突然 猛然 骤然 陡然 居然 竟然 果然 果真 当真 确实 的确 实在 真正 真实 真诚 诚恳 诚实 老实 忠厚 厚道 善良 仁慈 慈善 慈悲 同情 怜悯 怜惜 可惜 遗憾 抱歉 对不起 多谢 感谢 感激 感恩 感动 激动 兴奋 高兴 快乐 愉快 开心 欢乐 欢喜 喜悦 欣喜 欣慰 满意 满足 知足 安心 放心 省心 担心 操心 烦心 闹心 伤心 痛心 难过 难受 痛苦 苦恼 烦恼 忧愁 忧虑 焦虑 着急 焦急 焦躁 急躁 暴躁 愤怒 气愤 恼火 生气 不满 不服 不平 不甘 不愿 不想 不要 不能 不会 不可 不行 不得 不许 不准 禁止 阻止 阻碍 妨碍 干扰 打扰 扰乱 破坏 损坏 毁坏 毁灭 消灭 消除 清除 排除 解除 废除 取消 撤销 注销 去掉 除去 减少 降低 下降 减弱 削弱 缩小 缩短 减轻 减缓 减慢 变慢 加速 加快 增强 加强 增大 扩大 扩展 延伸 延长 提升 提高 改善 改良 改革 改造 转变 转化 转换 变更 变革 革命 革新 创造 创立 创办 建设 建造 制造 制作 制定 制订 拟定 起草 撰写 写作 书写 记录 记载 记述 描述 描写 描绘 叙述 讲述 陈述 阐释 阐明 表露 流露 透露 泄露 泄漏 披露 揭露 揭示 昭示 标明 标示 标识 意味 含有 囊括 包罗 容纳 包容 宽容 宽恕 饶恕 原谅 谅解 晓得 懂得 明白 醒悟 觉悟 觉醒 复苏 明了 必定 必需 祈求 乞求 乞讨 讨要 索要 索取 求取 追求 谋求 寻求 寻找 找寻 查找 查询 查问 询问 咨询 征询 建议 提议 倡议 主张 主意 从事 参与 参加 加入 进入 深入 侵入 渗透 渗入 融入 混合 掺杂 夹杂 含有 具有 拥有 具备 享有 获得 得到 取得 赢得 赚取 挣得 收获 收成 结局 结尾 末尾 末端 后期 后来 之后 以后 随后 接着 继而 连续 持续 继续 延续 继承 传承 流传 盛行 风行 时髦 时尚 潮流 趋向 走向 方向 宗旨 意图 企图 试图 打算 规划 策划 谋划 筹划 筹备 准备 预备 预先 事先 提前 趁早 及时 适时 当时 当场 当下 目前 当前 现在 如今 现今 当代 现代 近代 古代 远古 上古 中古 中世纪 时期 时代 年代 年度 年份 季度 月度 周度 日度 时刻 时候 时分 瞬间 刹那 片刻 须臾 短暂 长久 长期 短期 临时 暂时 暂且 姑且 权且 凑合 将就 勉强 强迫 强制 逼迫 被迫 被动 主动 积极 消极 正面 反面 侧面 负面 乐观 悲观 肯定 否定 认可 承认 确认 证实 验证 检验 检测 测试 考核 考查 考察 视察 巡视 巡查 检查 审查 审计 监察 监督 管制 抑制 压抑 压制 镇压 压迫 挤压 压缩 浓缩 凝聚 凝结 凝固 固定 稳定 稳固 牢固 坚固 坚强 坚定 坚决 坚毅 坚韧 坚忍 坚持 保守 拘谨 慎重 谨慎 小心 仔细 大意 马虎 草率 鲁莽 冲动 松弛 松懈 懈怠 懒惰 忙碌 清闲 悠闲 安逸 舒适 舒服 惬意 畅快 痛快 尽兴 过瘾 贪婪 吝啬 慷慨 大方 豪爽 豁达 开朗 向上 进取 奋进 拼搏 奋斗 斗争 竞争 竞赛 比赛 较量 衡量 权衡 斟酌 考虑 思考 思索 沉思 冥想 幻想 空想 梦想 理想 愿望 期望 盼望 渴望 希冀 奢求 妄想 野心 雄心 壮志 豪情 激情 热情 深情 痴情 多情 柔情 温情 亲情 友情 交情 人情 世故 圆滑 老练 成熟 稳重 沉着 冷静 理智 明智 聪明 智慧 才智 才华 才干 本领 本事 技能 技巧 技艺 手艺 工艺 技术 学术 学问 学识 见识 胆识 勇气 胆量 气魄 气势 气派 风度 风采 风姿 风韵 风味 风格 格调 品位 品味 趣味 情趣 情调 情怀 情意 情谊 情义 恩怨 情仇 爱恨 喜恶 好坏 优劣 高下 上下 左右 前后 内外 表里 虚实 真假 真伪 正邪 善恶 美丑 强弱 大小 多少 轻重 缓急 快慢 迟早 早晚 先后 主次 本末 始终 首尾 开合 聚散 离合 得失 成败 胜负 输赢 盈亏 增减 升降 沉浮 起落 兴衰 荣辱 利害 利弊 祸福 吉凶 忠奸 贤愚 智愚 巧拙 精粗 粗细 松紧 疏密 浓淡 深浅 远近 高低 长短 宽窄 厚薄 软硬 冷热 暖凉 干湿 燥润 枯荣 盛衰 兴亡 存亡 生死".split()
)


def build_flat_rules() -> List[Tuple[str, str, str]]:
    """
    将 LINK_RULES 展开为扁平列表，按关键词长度降序排列。
    这样 'Algebraic Geometry' 会优先于 'Geometry' 被匹配。
    """
    flat = []
    for keywords, link_text, target in LINK_RULES:
        for kw in keywords:
            flat.append((kw, link_text, target))
    # 去重：同义词可能指向同一目标，保留最长的
    seen = {}
    for kw, link_text, target in flat:
        key = (kw.lower(), target)
        if key not in seen or len(kw) > len(seen[key][0]):
            seen[key] = (kw, link_text, target)
    flat = list(seen.values())
    flat.sort(key=lambda x: len(x[0]), reverse=True)
    return flat


def split_by_backticks(text: str) -> List[Tuple[str, bool]]:
    """
    将文本按成对的反引号分割。
    返回 [(片段, 是否在反引号内), ...]
    """
    parts = []
    current = ""
    in_backtick = False
    for char in text:
        if char == "`":
            parts.append((current, in_backtick))
            current = ""
            in_backtick = not in_backtick
        else:
            current += char
    parts.append((current, in_backtick))
    return parts


def has_link_with_same_target(text: str, keyword: str, target: str) -> bool:
    """检查是否已经有指向同一目标的同名链接。"""
    return f"[{keyword}]({target})" in text


def linkify_cell(cell_text: str, flat_rules: List[Tuple[str, str, str]]) -> Tuple[str, int]:
    """
    对单个表格单元格添加链接。
    返回: (新文本, 链接数)
    """
    original = cell_text.strip()
    if not original:
        return cell_text, 0

    # 如果整个单元格已经是纯链接，跳过
    if re.match(r"^\[.*?\]\(.*?\)$", original.strip()):
        return cell_text, 0

    parts = split_by_backticks(cell_text)
    new_segments = []
    links_added = 0

    for seg, in_backtick in parts:
        if in_backtick:
            new_segments.append(seg)
            continue

        new_seg = seg
        replacements = []
        for keyword, link_text, target in flat_rules:
            pattern = re.compile(
                r"(?<![\u4e00-\u9fa5a-zA-Z0-9_.\-])"
                + re.escape(keyword)
                + r"(?![\u4e00-\u9fa5a-zA-Z0-9_.\-])"
            )
            for match in pattern.finditer(new_seg):
                matched_str = match.group(0)
                start, end = match.start(), match.end()
                # 避免与已计划替换的区域重叠
                if any(start < e and end > s for s, e, _, _ in replacements):
                    continue
                if has_link_with_same_target(new_seg, matched_str, target):
                    continue
                replacements.append((start, end, matched_str, target))

        if not replacements:
            new_segments.append(seg)
            continue

        # 从右到左排序，避免索引偏移
        replacements.sort(key=lambda x: x[0], reverse=True)
        for start, end, matched_str, target in replacements:
            new_seg = new_seg[:start] + f"[{matched_str}]({target})" + new_seg[end:]
            links_added += 1

        new_segments.append(new_seg)

    # 重组
    result = ""
    for i, (seg, in_bt) in enumerate(parts):
        if i > 0:
            result += "`"
        result += new_segments[i] if not in_bt else seg

    return result, links_added


def should_skip_cell(cell_text: str) -> bool:
    """判断是否应跳过该单元格的链接化。"""
    stripped = cell_text.strip()
    if not stripped:
        return True
    # 跳过纯标签/属性名
    if re.match(r"^\*?\*?(课程|教材|备注|覆盖度|对应|项目|文档|路径|关键|概念|学习时间|覆盖率|先修|学分|学时|学期|代码|名称|主题)\*?\*?$", stripped):
        return True
    # 跳过纯数字/百分比/emoji
    if re.match(r"^[0-9\s\-%\.🟢🟡🟠⚪⭐🔴/]+$", stripped):
        return True
    return False


def looks_like_path(text: str) -> bool:
    """判断文本是否看起来像文件路径或文档路径。"""
    if "docs/" in text or ".md" in text or "http" in text:
        return True
    if text.count("/") >= 1 and re.search(r"\d{2}-", text):
        return True
    return False


def extract_candidate_names(cell_text: str) -> List[str]:
    """从单元格中提取可能的课程/主题名称候选。"""
    stripped = cell_text.strip()
    if should_skip_cell(stripped):
        return []
    if looks_like_path(stripped):
        return []
    if "`" in stripped:
        return []
    candidates = []
    # 英文课程名: Capitalized words (2+ words)
    for m in re.finditer(r"[A-Z][a-zA-Z]+(?:\s+[A-Z][a-zA-Z]+)+", stripped):
        w = m.group(0)
        if len(w) > 3:
            candidates.append(w)
    # 中文学科名: 2-6个中文字符
    for m in re.finditer(r"[\u4e00-\u9fa5]{2,6}", stripped):
        w = m.group(0)
        if w not in COMMON_CHINESE_WORDS:
            candidates.append(w)
    return candidates


def process_file(filepath: Path, flat_rules: List[Tuple[str, str, str]], dry_run: bool = False) -> dict:
    """处理单个文件。"""
    content = filepath.read_text(encoding="utf-8")
    lines = content.splitlines()
    new_lines = []
    total_links = 0
    unmatched_candidates: Set[str] = set()
    modified = False

    for line in lines:
        if not line.strip().startswith("|"):
            new_lines.append(line)
            continue

        # 跳过分隔线行
        if re.match(r"^\s*\|(?:\s*:?-+:?\s*\|)+\s*$", line):
            new_lines.append(line)
            continue

        cells = line.split("|")
        new_cells = []
        for cell in cells:
            if should_skip_cell(cell):
                for c in extract_candidate_names(cell):
                    unmatched_candidates.add(c)
                new_cells.append(cell)
                continue

            new_cell, links = linkify_cell(cell, flat_rules)
            if links > 0:
                total_links += links
                modified = True
            else:
                for c in extract_candidate_names(cell):
                    unmatched_candidates.add(c)
            new_cells.append(new_cell)
        new_lines.append("|".join(new_cells))

    result = {
        "filepath": filepath,
        "links_added": total_links,
        "modified": modified,
        "unmatched": sorted(unmatched_candidates),
    }

    if modified and not dry_run:
        filepath.write_text("\n".join(new_lines) + ("\n" if content.endswith("\n") else ""), encoding="utf-8")

    return result


def main():
    parser = argparse.ArgumentParser(description="为课程对齐文档自动添加指向 docs/ 的超链接")
    parser.add_argument("--dry-run", action="store_true", help="预览模式，不实际写入文件")
    parser.add_argument("--project-dir", default="project", help="project 目录路径")
    args = parser.parse_args()

    root = Path(__file__).parent.parent
    project_dir = root / args.project_dir

    if not project_dir.exists():
        print(f"错误: 目录不存在 {project_dir}", file=sys.stderr)
        sys.exit(1)

    flat_rules = build_flat_rules()

    matched_files = []
    pattern = re.compile(r"course-mapping|alignment|课程对齐|course_mapping|mapping-detailed", re.I)
    for f in project_dir.iterdir():
        if f.is_file() and f.suffix == ".md" and pattern.search(f.name):
            matched_files.append(f)

    matched_files.sort()

    if not matched_files:
        print("未找到匹配的文件。")
        sys.exit(0)

    print(f"发现 {len(matched_files)} 个待处理文件:\n")
    for f in matched_files:
        print(f"  - {f.name}")
    print()

    total_links = 0
    all_unmatched: Set[str] = set()
    modified_files = []

    for f in matched_files:
        result = process_file(f, flat_rules, dry_run=args.dry_run)
        total_links += result["links_added"]
        if result["modified"]:
            modified_files.append(f.name)
        if result["links_added"]:
            print(f"  {f.name}: +{result['links_added']} 个链接")
        all_unmatched.update(result["unmatched"])

    print(f"\n{'='*50}")
    print(f"处理文件数: {len(matched_files)}")
    print(f"添加链接数: {total_links}")
    if args.dry_run:
        print("模式: --dry-run (未实际写入)")
    else:
        print(f"已修改文件数: {len(modified_files)}")

    if all_unmatched:
        print(f"\n未能匹配的候选名称示例 (前20个):")
        for name in list(all_unmatched)[:20]:
            print(f"  - {name}")


if __name__ == "__main__":
    main()
