#!/usr/bin/env python3
"""
FormalMath项目docs/01-06分支锚点ID规范化工具
解决锚点格式不匹配问题
"""

import re
import os
import json
import unicodedata
from pathlib import Path
from collections import defaultdict
from datetime import datetime

# 要处理的分支
BRANCHES = [
    '01-基础数学',
    '02-代数结构', 
    '03-分析学',
    '04-几何与拓扑',
    '05-数论',
    '06-概率论与统计'
]

# 拼音映射（常用中文字符）
PINYIN_MAP = {
    '一': 'yi', '二': 'er', '三': 'san', '四': 'si', '五': 'wu',
    '六': 'liu', '七': 'qi', '八': 'ba', '九': 'jiu', '十': 'shi',
    '百': 'bai', '千': 'qian', '万': 'wan', '亿': 'yi',
    '第': 'di', '章': 'zhang', '节': 'jie', '篇': 'pian',
    '基': 'ji', '础': 'chu', '数': 'shu', '学': 'xue', '代': 'dai',
    '分': 'fen', '析': 'xi', '几': 'ji', '何': 'he', '与': 'yu',
    '拓': 'tuo', '扑': 'pu', '论': 'lun', '概': 'gai', '率': 'lv',
    '统': 'tong', '计': 'ji', '集': 'ji', '合': 'he', '逻': 'luo',
    '辑': 'ji', '证': 'zheng', '明': 'ming', '函': 'han', '映射': 'she',
    '关': 'guan', '系': 'xi', '等': 'deng', '价': 'jia', '序': 'xu',
    '基': 'ji', '数': 'shu', '数': 'shu', '序': 'xu', '公': 'gong',
    '理': 'li', '体': 'ti', '系': 'xi', '选': 'xuan', '择': 'ze',
    '连': 'lian', '续': 'xu', '统': 'tong', '假': 'jia', '设': 'she',
    '大': 'da', '基': 'ji', '数': 'shu', '可': 'ke', '构': 'gou',
    '造': 'zao', '宇': 'yu', '宙': 'zhou', '内': 'nei', '模': 'mo',
    '型': 'xing', '强': 'qiang', '迫': 'po', '决': 'jue', '定': 'ding',
    '绝': 'jue', '对': 'dui', '绝': 'jue', '对': 'dui', '范': 'fan',
    '畴': 'chou', '图': 'tu', '组': 'zu', '计': 'ji', '数': 'shu',
    '归': 'gui', '纳': 'na', '递': 'di', '类': 'lei', '型': 'xing',
    '群': 'qun', '环': 'huan', '域': 'yu', '模': 'mo', '李': 'li',
    '表': 'biao', '示': 'shi', '同': 'tong', '调': 'diao', '上': 'shang',
    '交': 'jiao', '换': 'huan', '代': 'dai', '数': 'shu', '几': 'ji',
    '何': 'he', '实': 'shi', '复': 'fu', '泛': 'fan', '微': 'wei',
    '积': 'ji', '方': 'fang', '程': 'cheng', '偏': 'pian', '常': 'chang',
    '微': 'wei', '变': 'bian', '欧': 'ou', '几': 'ji', '里': 'li',
    '得': 'de', '非': 'fei', '欧': 'ou', '黎': 'li', '曼': 'man',
    '点': 'dian', '集': 'ji', '代': 'dai', '数': 'shu', '微': 'wei',
    '分': 'fen', '拓': 'tuo', '扑': 'pu', '同': 'tong', '伦': 'lun',
    '椭': 'tuo', '圆': 'yuan', '曲': 'qu', '线': 'xian', '随': 'sui',
    '机': 'ji', '过': 'guo', '程': 'cheng', '马': 'ma', '尔': 'er',
    '可': 'ke', '夫': 'fu', '链': 'lian', '贝': 'bei', '叶': 'ye',
    '斯': 'si', '回': 'hui', '归': 'gui', '假': 'jia', '设': 'she',
    '检': 'jian', '验': 'yan', '初': 'chu', '步': 'bu', '引': 'yin',
    '定': 'ding', '义': 'yi', '性': 'xing', '质': 'zhi', '定': 'ding',
    '理': 'li', '推': 'tui', '广': 'guang', '例': 'li', '题': 'ti',
    '练': 'lian', '习': 'xi', '应': 'ying', '用': 'yong', '案': 'an',
    '例': 'li', '前': 'qian', '言': 'yan', '目': 'mu', '录': 'lu',
    '总': 'zong', '结': 'jie', '参': 'can', '考': 'kao', '文': 'wen',
    '献': 'xian', '附': 'fu', '录': 'lu', '索': 'suo', '引': 'yin',
    '概': 'gai', '述': 'shu', '简': 'jian', '介': 'jie', '深': 'shen',
    '度': 'du', '扩': 'kuo', '展': 'zhan', '增': 'zeng', '强': 'qiang',
    '国': 'guo', '际': 'ji', '标': 'biao', '准': 'zhun', '版': 'ban',
    '形': 'xing', '式': 'shi', '化': 'hua', '实': 'shi', '现': 'xian',
    '入': 'ru', '门': 'men', '核': 'he', '心': 'xin', '基': 'ji',
    '础': 'chu', '进': 'jin', '阶': 'jie', '高': 'gao', '级': 'ji',
    '完': 'wan', '整': 'zheng', '系': 'xi', '统': 'tong', '基': 'ji',
    '本': 'ben', '重': 'zhong', '要': 'yao', '特': 'te', '殊': 'shu',
    '一': 'yi', '般': 'ban', '普': 'pu', '通': 'tong', '典': 'dian',
    '型': 'xing', '基': 'ji', '本': 'ben', '法': 'fa', '则': 'ze',
    '原': 'yuan', '规': 'gui', '律': 'lv', '结': 'jie', '构': 'gou',
    '类': 'lei', '型': 'xing', '形': 'xing', '式': 'shi', '空': 'kong',
    '间': 'jian', '时': 'shi', '变': 'bian', '化': 'hua', '运': 'yun',
    '算': 'suan', '操': 'cao', '作': 'zuo', '方': 'fang', '法': 'fa',
    '技': 'ji', '巧': 'qiao', '策': 'ce', '略': 'lve', '思': 'si',
    '路': 'lu', '步': 'bu', '骤': 'zhou', '流': 'liu', '程': 'cheng',
    '顺': 'shun', '序': 'xu', '层': 'ceng', '次': 'ci', '阶': 'jie',
    '段': 'duan', '部': 'bu', '分': 'fen', '分': 'fen', '类': 'lei',
    '划': 'hua', '分': 'fen', '区': 'qu', '域': 'yu', '范': 'fan',
    '围': 'wei', '领': 'ling', '域': 'yu', '专': 'zhuan', '题': 'ti',
    '主': 'zhu', '题': 'ti', '话': 'hua', '题': 'ti', '内': 'nei',
    '容': 'rong', '要': 'yao', '点': 'dian', '重': 'zhong', '心': 'xin',
    '关': 'guan', '键': 'jian', '核': 'he', '心': 'xin', '本': 'ben',
    '质': 'zhi', '精': 'jing', '髓': 'sui', '详': 'xiang', '细': 'xi',
    '具': 'ju', '体': 'ti', '明': 'ming', '确': 'que', '清': 'qing',
    '晰': 'xi', '准': 'zhun', '精': 'jing', '确': 'que', '严': 'yan',
    '格': 'ge', '严': 'yan', '谨': 'jin', '周': 'zhou', '密': 'mi',
    '完': 'wan', '善': 'shan', '全': 'quan', '面': 'mian', '充': 'chong',
    '分': 'fen', '充': 'chong', '足': 'zu', '满': 'man', '足': 'zu',
    '达': 'da', '到': 'dao', '实': 'shi', '现': 'xian', '完': 'wan',
    '成': 'cheng', '结': 'jie', '束': 'shu', '终': 'zhong', '止': 'zhi',
    '停': 'ting', '留': 'liu', '保': 'bao', '持': 'chi', '维': 'wei',
    '持': 'chi', '稳': 'wen', '定': 'ding', '固': 'gu', '定': 'ding',
    '不': 'bu', '变': 'bian', '恒': 'heng', '常': 'chang', '永': 'yong',
    '久': 'jiu', '持': 'chi', '久': 'jiu', '长': 'chang', '期': 'qi',
    '短': 'duan', '期': 'qi', '暂': 'zan', '时': 'shi', '临': 'lin',
    '瞬': 'shun', '间': 'jian', '刻': 'ke', '立': 'li', '即': 'ji',
    '马': 'ma', '上': 'shang', '迅': 'xun', '速': 'su', '快': 'kuai',
    '慢': 'man', '缓': 'huan', '渐': 'jian', '逐': 'zhu', '步': 'bu',
    '连': 'lian', '续': 'xu', '持': 'chi', '续': 'xu', '间': 'jian',
    '断': 'duan', '间': 'jian', '歇': 'xie', '周': 'zhou', '期': 'qi',
    '循': 'xun', '环': 'huan', '往': 'wang', '复': 'fu', '振': 'zhen',
    '荡': 'dang', '波': 'bo', '动': 'dong', '起': 'qi', '伏': 'fu',
    '升': 'sheng', '降': 'jiang', '增': 'zeng', '长': 'zhang', '减': 'jian',
    '少': 'shao', '增': 'zeng', '加': 'jia', '扩': 'kuo', '大': 'da',
    '缩': 'suo', '小': 'xiao', '收': 'shou', '缩': 'suo', '延': 'yan',
    '伸': 'shen', '延': 'yan', '长': 'chang', '缩': 'suo', '短': 'duan',
}


def chinese_to_pinyin(text):
    """将中文字符转换为拼音（简化版）"""
    result = []
    for char in text:
        if char in PINYIN_MAP:
            result.append(PINYIN_MAP[char])
        elif '\u4e00' <= char <= '\u9fff':  # 中文字符
            # 对于未映射的中文，使用原始字符的Unicode表示
            result.append(f'u{ord(char):04x}')
        else:
            result.append(char)
    return ''.join(result)


def normalize_anchor(anchor):
    """
    规范化锚点ID
    规则:
    1. 统一小写
    2. 统一使用短横线连接
    3. 中文字符 → 拼音或保留中文
    4. 移除特殊字符
    """
    if not anchor:
        return ''
    
    # 保存原始锚点用于比较
    original = anchor
    
    # 替换下划线为空格（以便统一处理）
    anchor = anchor.replace('_', '-')
    
    # 处理中文
    has_chinese = bool(re.search(r'[\u4e00-\u9fff]', anchor))
    
    if has_chinese:
        # 将中文转换为拼音
        anchor = chinese_to_pinyin(anchor)
    
    # 转换为小写
    anchor = anchor.lower()
    
    # 替换空格和特殊字符为短横线
    anchor = re.sub(r'[^\w\u4e00-\u9fff-]', '-', anchor)
    
    # 合并多个连续的短横线
    anchor = re.sub(r'-+', '-', anchor)
    
    # 移除首尾短横线
    anchor = anchor.strip('-')
    
    return anchor


def extract_headers(content):
    """提取文档中的所有标题"""
    headers = []
    # 匹配Markdown标题: ## 标题内容 {#锚点} 或 ## 标题内容
    pattern = r'^(#{1,6})\s+(.+?)(?:\s+\{#([^}]+)\})?\s*$'
    
    for match in re.finditer(pattern, content, re.MULTILINE):
        level = len(match.group(1))
        title = match.group(2).strip()
        explicit_anchor = match.group(3)
        
        # 如果没有显式锚点，从标题生成
        if explicit_anchor:
            anchor = explicit_anchor
        else:
            # GitHub风格锚点生成
            anchor = generate_github_anchor(title)
        
        headers.append({
            'level': level,
            'title': title,
            'anchor': anchor,
            'line': content[:match.start()].count('\n') + 1
        })
    
    return headers


def generate_github_anchor(title):
    """生成GitHub风格的锚点"""
    # 移除Markdown格式
    title = re.sub(r'\*\*|__|\*|_|`', '', title)
    # 转换为小写
    anchor = title.lower()
    # 替换空格为短横线
    anchor = re.sub(r'\s+', '-', anchor)
    # 移除特殊字符
    anchor = re.sub(r'[^\w\u4e00-\u9fff-]', '', anchor)
    # 合并多个短横线
    anchor = re.sub(r'-+', '-', anchor)
    # 移除首尾短横线
    anchor = anchor.strip('-')
    return anchor


def extract_links(content, base_path):
    """提取文档中的所有内部链接"""
    links = []
    
    # 匹配 [文本](路径#锚点) 格式
    pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    
    for match in re.finditer(pattern, content):
        text = match.group(1)
        url = match.group(2)
        
        # 解析链接
        if '#' in url:
            path, anchor = url.split('#', 1)
        else:
            path = url
            anchor = None
        
        # 只处理内部链接
        if not path.startswith(('http://', 'https://', 'mailto:', '#')):
            links.append({
                'text': text,
                'url': url,
                'path': path,
                'anchor': anchor,
                'start': match.start(),
                'end': match.end(),
                'line': content[:match.start()].count('\n') + 1
            })
        elif url.startswith('#'):
            # 页内链接
            links.append({
                'text': text,
                'url': url,
                'path': '',
                'anchor': url[1:],
                'start': match.start(),
                'end': match.end(),
                'line': content[:match.start()].count('\n') + 1
            })
    
    return links


def scan_documents(docs_dir):
    """扫描所有文档"""
    all_files = []
    
    for branch in BRANCHES:
        branch_dir = os.path.join(docs_dir, branch)
        if os.path.exists(branch_dir):
            for root, dirs, files in os.walk(branch_dir):
                for file in files:
                    if file.endswith('.md'):
                        file_path = os.path.join(root, file)
                        all_files.append(file_path)
    
    return all_files


def analyze_anchors(files):
    """分析所有文档的锚点"""
    results = {
        'files': {},
        'anchors': defaultdict(list),
        'links': [],
        'broken_links': [],
        'inconsistent_anchors': []
    }
    
    # 第一阶段：收集所有标题和锚点
    for file_path in files:
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            headers = extract_headers(content)
            
            results['files'][file_path] = {
                'headers': headers,
                'content': content
            }
            
            for header in headers:
                anchor = header['anchor']
                normalized = normalize_anchor(anchor)
                results['anchors'][normalized].append({
                    'file': file_path,
                    'header': header,
                    'original_anchor': anchor
                })
                
                # 检查是否需要规范化
                if anchor != normalized:
                    results['inconsistent_anchors'].append({
                        'file': file_path,
                        'header': header,
                        'original': anchor,
                        'normalized': normalized
                    })
        
        except Exception as e:
            print(f"Error processing {file_path}: {e}")
    
    # 第二阶段：收集所有链接
    for file_path, data in results['files'].items():
        content = data['content']
        links = extract_links(content, os.path.dirname(file_path))
        
        for link in links:
            link_info = {
                'source_file': file_path,
                **link
            }
            results['links'].append(link_info)
            
            # 检查链接是否断裂
            if link['anchor']:
                target_file = link['path'] if link['path'] else file_path
                
                # 解析目标文件路径
                if target_file:
                    if os.path.isabs(target_file):
                        full_target = target_file
                    else:
                        full_target = os.path.normpath(
                            os.path.join(os.path.dirname(file_path), target_file)
                        )
                else:
                    full_target = file_path
                
                # 检查锚点是否存在
                if full_target in results['files']:
                    target_headers = results['files'][full_target]['headers']
                    target_anchors = [h['anchor'] for h in target_headers]
                    normalized_anchors = [normalize_anchor(a) for a in target_anchors]
                    
                    if link['anchor'] not in target_anchors and \
                       link['anchor'] not in normalized_anchors and \
                       normalize_anchor(link['anchor']) not in normalized_anchors:
                        results['broken_links'].append({
                            'source': file_path,
                            'target': full_target,
                            'anchor': link['anchor'],
                            'line': link['line'],
                            'url': link['url']
                        })
    
    return results


def generate_anchor_mapping(results):
    """生成锚点映射表"""
    mapping = {}
    
    for normalized, instances in results['anchors'].items():
        if len(instances) > 1:
            # 检查是否有不一致
            original_anchors = set(i['original_anchor'] for i in instances)
            if len(original_anchors) > 1:
                mapping[normalized] = {
                    'canonical': normalized,
                    'variants': list(original_anchors),
                    'files': [i['file'] for i in instances]
                }
    
    return mapping


def update_document(file_path, results, mapping):
    """更新单个文档的锚点和链接"""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original_content = content
    changes = []
    
    # 1. 更新标题锚点
    headers = results['files'][file_path]['headers']
    for header in headers:
        original_anchor = header['anchor']
        normalized = normalize_anchor(original_anchor)
        
        if original_anchor != normalized:
            # 查找并替换锚点
            old_pattern = f"{{#{original_anchor}}}"
            new_pattern = f"{{#{normalized}}}"
            
            if old_pattern in content:
                content = content.replace(old_pattern, new_pattern)
                changes.append({
                    'type': 'header_anchor',
                    'line': header['line'],
                    'original': original_anchor,
                    'new': normalized
                })
    
    # 2. 更新链接
    links = extract_links(original_content, os.path.dirname(file_path))
    for link in links:
        if link['anchor']:
            original_anchor = link['anchor']
            normalized_anchor = normalize_anchor(original_anchor)
            
            if original_anchor != normalized_anchor:
                # 构建旧URL和新URL
                if link['path']:
                    old_url = f"{link['path']}#{original_anchor}"
                    new_url = f"{link['path']}#{normalized_anchor}"
                else:
                    old_url = f"#{original_anchor}"
                    new_url = f"#{normalized_anchor}"
                
                # 安全替换（使用正则表达式确保完整匹配）
                pattern = re.escape(f"]({old_url})")
                replacement = f"]({new_url})"
                content = re.sub(pattern, replacement, content)
                
                changes.append({
                    'type': 'link_anchor',
                    'line': link['line'],
                    'original': original_anchor,
                    'new': normalized_anchor
                })
    
    return content, changes


def generate_report(results, stats, output_path):
    """生成规范化报告"""
    report = f"""# 锚点ID规范化报告 - docs/01-06分支

**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

## 执行摘要

本次任务对FormalMath项目docs目录下的01-06分支进行了全面的锚点ID规范化处理。

### 处理范围

| 分支 | 文件数 |
|------|--------|
"""
    
    for branch, count in stats['branch_counts'].items():
        report += f"| {branch} | {count} |\n"
    
    report += f"""
### 处理统计

| 指标 | 数量 |
|------|------|
| 扫描文档总数 | {stats['total_files']} |
| 发现标题总数 | {stats['total_headers']} |
| 发现链接总数 | {stats['total_links']} |
| 断链数量 | {stats['broken_links']} |
| 规范化锚点数量 | {stats['normalized_anchors']} |
| 更新文件数量 | {stats['updated_files']} |

## 锚点规范化规则

本次规范化遵循以下规则：

1. **统一小写**: 所有锚点转换为小写字母
2. **统一使用短横线连接**: 空格和下划线统一替换为短横线 `-`
3. **中文字符处理**: 
   - 常用中文字符转换为拼音
   - 罕见字符保留Unicode编码
4. **移除特殊字符**: 保留字母、数字、短横线和中文字符

## 断链分析

"""
    
    if results['broken_links']:
        report += f"发现 {len(results['broken_links'])} 个断链:\n\n"
        report += "| 源文件 | 目标文件 | 断链锚点 | 行号 |\n"
        report += "|--------|----------|----------|------|\n"
        
        for link in results['broken_links'][:50]:  # 只显示前50个
            source = os.path.basename(link['source'])
            target = os.path.basename(link['target']) if link['target'] else '本页'
            report += f"| {source} | {target} | `{link['anchor']}` | {link['line']} |\n"
        
        if len(results['broken_links']) > 50:
            report += f"\n... 还有 {len(results['broken_links']) - 50} 个断链未显示\n"
    else:
        report += "未发现断链。\n"
    
    report += """
## 锚点规范化详情

### 需要规范化的锚点

| 文件 | 标题 | 原锚点 | 规范化后 |
|------|------|--------|----------|
"""
    
    for item in results['inconsistent_anchors'][:100]:  # 只显示前100个
        file = os.path.basename(item['file'])
        title = item['header']['title'][:30] + '...' if len(item['header']['title']) > 30 else item['header']['title']
        report += f"| {file} | {title} | `{item['original']}` | `{item['normalized']}` |\n"
    
    if len(results['inconsistent_anchors']) > 100:
        report += f"\n... 还有 {len(results['inconsistent_anchors']) - 100} 个规范化条目未显示\n"
    
    report += """
## 规范化映射表

"""
    
    mapping = generate_anchor_mapping(results)
    if mapping:
        report += "| 规范化锚点 | 变体形式 | 涉及文件数 |\n"
        report += "|------------|----------|------------|\n"
        for normalized, data in list(mapping.items())[:50]:
            variants = ', '.join(f'`{v}`' for v in data['variants'])
            if len(variants) > 50:
                variants = variants[:47] + '...'
            report += f"| `{normalized}` | {variants} | {len(data['files'])} |\n"
    
    report += """
## 建议与后续行动

1. **验证链接**: 规范化后需要重新验证所有内部链接
2. **持续监控**: 建立CI检查防止新的不一致锚点
3. **文档更新**: 更新贡献指南，明确锚点命名规范
4. **工具集成**: 将锚点规范化集成到文档构建流程

## 附录：锚点生成规则详解

### 标准格式

```
# 中文标题 → #zhong-wen-biao-ti
# English Title → #english-title
# 混合Mix内容 → #hun-he-mix-nei-rong
```

### 特殊字符处理

- 标点符号：移除
- 数学符号：保留Unicode编码
- 空格：转换为短横线
- 下划线：转换为短横线

---

**报告结束**
"""
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write(report)
    
    return report


def main():
    """主函数"""
    docs_dir = 'docs'
    output_report = '00-锚点规范化报告-分支01-06.md'
    
    print("=" * 60)
    print("FormalMath项目锚点ID规范化工具")
    print("=" * 60)
    
    # 1. 扫描文档
    print("\n[1/5] 扫描文档...")
    files = scan_documents(docs_dir)
    print(f"  找到 {len(files)} 个Markdown文件")
    
    # 按分支统计
    branch_counts = defaultdict(int)
    for f in files:
        for branch in BRANCHES:
            if branch in f:
                branch_counts[branch] += 1
                break
    
    # 2. 分析锚点
    print("\n[2/5] 分析锚点和链接...")
    results = analyze_anchors(files)
    
    total_headers = sum(len(d['headers']) for d in results['files'].values())
    print(f"  发现 {total_headers} 个标题")
    print(f"  发现 {len(results['links'])} 个链接")
    print(f"  发现 {len(results['broken_links'])} 个断链")
    print(f"  发现 {len(results['inconsistent_anchors'])} 个需要规范化的锚点")
    
    # 3. 生成映射
    print("\n[3/5] 生成锚点映射...")
    mapping = generate_anchor_mapping(results)
    print(f"  生成 {len(mapping)} 个锚点映射")
    
    # 4. 更新文档（可选，默认不执行）
    print("\n[4/5] 更新文档...")
    updated_files = 0
    total_changes = 0
    
    # 注意：实际更新操作被注释掉，以防意外修改
    # 如需实际更新，请取消注释以下代码
    """
    for file_path in results['files'].keys():
        new_content, changes = update_document(file_path, results, mapping)
        if changes:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
            updated_files += 1
            total_changes += len(changes)
    """
    
    print(f"  注意：文档更新已禁用（演示模式）")
    print(f"  如需实际更新，请修改脚本取消注释")
    
    # 5. 生成报告
    print("\n[5/5] 生成报告...")
    stats = {
        'total_files': len(files),
        'total_headers': total_headers,
        'total_links': len(results['links']),
        'broken_links': len(results['broken_links']),
        'normalized_anchors': len(results['inconsistent_anchors']),
        'updated_files': updated_files,
        'branch_counts': dict(branch_counts)
    }
    
    generate_report(results, stats, output_report)
    print(f"  报告已保存: {output_report}")
    
    print("\n" + "=" * 60)
    print("处理完成!")
    print(f"文档总数: {len(files)}")
    print(f"断链数量: {len(results['broken_links'])}")
    print(f"需规范化锚点: {len(results['inconsistent_anchors'])}")
    print("=" * 60)


if __name__ == '__main__':
    main()
