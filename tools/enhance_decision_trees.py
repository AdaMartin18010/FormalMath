#!/usr/bin/env python3
"""
FormalMath 决策树批量优化脚本

功能：
1. 检查决策树文件结构完整性
2. 添加缺失的标准章节
3. 更新工具与资源链接
4. 添加检查清单模板
5. 添加常见问题模板
"""

import os
import re
from pathlib import Path

def get_all_decision_trees(directory):
    """获取所有决策树文件（不包括索引文件）"""
    dt_files = []
    for f in os.listdir(directory):
        if f.endswith('.md') and not f.startswith('00-'):
            dt_files.append(os.path.join(directory, f))
    return sorted(dt_files)

def read_file(filepath):
    """读取文件内容"""
    with open(filepath, 'r', encoding='utf-8') as f:
        return f.read()

def write_file(filepath, content):
    """写入文件内容"""
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)

def has_section(content, section_name):
    """检查是否有特定章节"""
    pattern = rf'^## {re.escape(section_name)}'
    return bool(re.search(pattern, content, re.MULTILINE))

def add_section_after(content, after_section, new_section_content):
    """在指定章节后添加新章节"""
    # 找到after_section的位置
    pattern = rf'(## {re.escape(after_section)}.*?)(?=## |\Z)'
    match = re.search(pattern, content, re.DOTALL | re.MULTILINE)
    if match:
        insert_pos = match.end()
        return content[:insert_pos] + new_section_content + content[insert_pos:]
    return content

def get_checklist_template():
    """获取检查清单模板"""
    return """
## 检查清单

### 决策前检查

- [ ] 已明确问题的类型和条件
- [ ] 已收集必要的信息
- [ ] 已排除明显的错误路径

### 执行过程检查

- [ ] 按照决策树路径逐步分析
- [ ] 记录每个决策节点的选择
- [ ] 验证中间结果的正确性

### 结果验证检查

- [ ] 结果符合预期
- [ ] 已通过替代方法验证（如适用）
- [ ] 边界情况已考虑

"""

def get_faq_template():
    """获取常见问题模板"""
    return """
## 常见问题

### Q: 如何确定我选择的决策路径是正确的？

**A**: 
1. 回顾每个决策节点的条件是否符合
2. 使用检查清单验证
3. 如果可能，用替代方法交叉验证结果

### Q: 如果决策树没有覆盖我的特殊情况怎么办？

**A**:
1. 查看"相关决策树"寻找更具体的指导
2. 在Math StackExchange等社区寻求帮助
3. 记录特殊情况，作为决策树改进建议反馈

### Q: 决策树推荐的方法不起作用怎么办？

**A**:
1. 检查是否正确执行了所有步骤
2. 回顾决策路径，看是否有误判
3. 尝试决策树中提到的替代方法
4. 寻求导师或同学的帮助

"""

def get_tools_resources_template():
    """获取工具与资源模板"""
    return """
## 工具与资源

### 推荐软件

| 软件 | 用途 | 平台 | 费用 |
|-----|------|------|------|
| **Mathematica** | 符号计算、可视化 | 全平台 | 付费 |
| **MATLAB** | 数值计算、仿真 | 全平台 | 付费/教育版 |
| **Python + NumPy/SciPy** | 科学计算 | 全平台 | 免费 |
| **SageMath** | 开源数学软件 | 全平台 | 免费 |
| **GeoGebra** | 几何可视化 | 全平台 | 免费 |

### 在线资源

| 资源 | 类型 | 说明 |
|-----|------|------|
| **Math StackExchange** | 社区 | 数学问答社区 |
| **Wikipedia** | 参考 | 数学概念查询 |
| **arXiv** | 论文 | 数学研究论文 |
| **GitHub** | 代码 | 数学相关开源项目 |

### 推荐教材与参考

- 根据具体决策树内容推荐相关教材
- 查阅相关领域的经典著作
- 参考在线课程和视频讲解

"""

def enhance_decision_tree(filepath):
    """优化单个决策树文件"""
    print(f"处理: {os.path.basename(filepath)}")
    
    content = read_file(filepath)
    modified = False
    
    # 添加检查清单（如果不存在）
    if not has_section(content, '检查清单'):
        # 尝试在"示例"或"方法详解"后添加
        if has_section(content, '示例'):
            content = add_section_after(content, '示例', get_checklist_template())
            modified = True
        elif has_section(content, '方法详解'):
            content = add_section_after(content, '方法详解', get_checklist_template())
            modified = True
        elif has_section(content, '核心策略'):
            content = add_section_after(content, '核心策略', get_checklist_template())
            modified = True
        elif has_section(content, '路径说明'):
            content = add_section_after(content, '路径说明', get_checklist_template())
            modified = True
    
    # 添加常见问题（如果不存在）
    if not has_section(content, '常见问题'):
        if has_section(content, '检查清单'):
            content = add_section_after(content, '检查清单', get_faq_template())
            modified = True
    
    # 添加工具与资源（如果不存在）
    if not has_section(content, '工具与资源'):
        # 在示例或核心策略后添加
        if has_section(content, '示例'):
            content = add_section_after(content, '示例', get_tools_resources_template())
            modified = True
        elif has_section(content, '核心策略'):
            content = add_section_after(content, '核心策略', get_tools_resources_template())
            modified = True
        elif has_section(content, '方法详解'):
            content = add_section_after(content, '方法详解', get_tools_resources_template())
            modified = True
    
    if modified:
        write_file(filepath, content)
        print(f"  ✓ 已优化")
    else:
        print(f"  - 无需修改")
    
    return modified

def add_related_trees_section(filepath, all_files):
    """添加相关决策树章节"""
    content = read_file(filepath)
    
    if has_section(content, '相关决策树'):
        return False
    
    filename = os.path.basename(filepath)
    
    # 根据文件名确定相关决策树
    related = []
    
    if '分析' in filename or '极限' in filename or '积分' in filename:
        related = ['01-分析学学习路径决策.md', '19-收敛性证明策略.md', '06-极限求解方法决策.md']
    elif '代数' in filename or '群' in filename or '环' in filename:
        related = ['02-代数学学习路径决策.md', '10-代数结构分类决策.md', '24-群论问题求解策略.md']
    elif '几何' in filename or '拓扑' in filename:
        related = ['03-几何学习路径决策.md', '11-拓扑性质证明策略.md']
    elif '概率' in filename or '统计' in filename:
        related = ['04-应用数学方向决策.md', '12-概率分布选择决策.md']
    elif '学习' in filename or '计划' in filename:
        related = ['00-学习策略决策树索引.md', '24-教材选择决策.md']
    elif '诊断' in filename or '困难' in filename:
        related = ['34-理解困难诊断.md', '35-计算错误诊断.md', '36-证明困难诊断.md']
    else:
        related = ['00-决策树使用指南.md']
    
    # 过滤掉自身
    related = [r for r in related if r != filename][:5]
    
    if not related:
        return False
    
    section_content = "\n## 相关决策树\n\n"
    for r in related:
        name = r.replace('.md', '').split('-', 1)[1] if '-' in r else r.replace('.md', '')
        section_content += f"- [{name}](./{r})\n"
    
    section_content += "\n"
    
    # 在文件末尾添加
    if not content.endswith('\n'):
        content += '\n'
    
    content += section_content
    content += "---\n\n*本决策树是FormalMath项目的一部分*\n"
    
    write_file(filepath, content)
    return True

def main():
    """主函数"""
    # 决策树目录
    dt_dir = Path('g:/_src/FormalMath/docs/decision-trees')
    
    if not dt_dir.exists():
        print(f"错误: 目录不存在 {dt_dir}")
        return
    
    print(f"决策树目录: {dt_dir}")
    print("="*60)
    
    # 获取所有决策树文件
    files = get_all_decision_trees(dt_dir)
    print(f"找到 {len(files)} 个决策树文件")
    print()
    
    # 统计
    enhanced_count = 0
    related_added_count = 0
    
    # 处理每个文件
    for filepath in files:
        # 基础优化
        if enhance_decision_tree(filepath):
            enhanced_count += 1
        
        # 添加相关决策树章节
        if add_related_trees_section(filepath, files):
            related_added_count += 1
            print(f"  ✓ 已添加相关决策树章节")
    
    print()
    print("="*60)
    print(f"优化完成!")
    print(f"  - 增强文件数: {enhanced_count}")
    print(f"  - 添加相关决策树章节: {related_added_count}")

if __name__ == '__main__':
    main()
