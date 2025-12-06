import re

file_path = r"e:\_src\FormalMath\数学家理念体系\高斯数学理念\02-数学内容深度分析\01-数论贡献\08-二次型表示数问题.md"

with open(file_path, 'r', encoding='utf-8') as f:
    lines = f.readlines()

new_lines = []
i = 0
while i < len(lines):
    line = lines[i]
    
    # 如果这一行是独立的 ```
    if line.strip() == '```':
        # 检查前面是否有 ```text
        has_text_start = False
        for j in range(max(0, i-200), i):
            if lines[j].strip() == '```text':
                has_text_start = True
                break
        
        # 如果前面没有 ```text，且下一行有内容，则是开始标记
        if not has_text_start and i + 1 < len(lines):
            next_line = lines[i + 1].strip()
            if next_line != '' and next_line != '```':
                new_lines.append('```text\n')
            else:
                new_lines.append(line)
        else:
            new_lines.append(line)
    else:
        new_lines.append(line)
    
    i += 1

content = ''.join(new_lines)
# 确保结束标记是 ```
content = re.sub(r'```text\n```', '```\n```', content)

with open(file_path, 'w', encoding='utf-8') as f:
    f.write(content)

print("Fixed!")
