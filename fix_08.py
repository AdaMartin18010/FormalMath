import re

file_path = r"e:\_src\FormalMath\数学家理念体系\高斯数学理念\02-数学内容深度分析\01-数论贡献\08-二次型表示数问题.md"

with open(file_path, 'r', encoding='utf-8') as f:
    content = f.read()

# 将独立的 ``` 行改为 ```text（开始标记）
# 但需要确保不是结束标记
lines = content.split('\n')
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
        
        # 如果前面没有 ```text，且下一行有内容（不是空行或```），则是开始标记
        if not has_text_start and i + 1 < len(lines):
            next_line = lines[i + 1].strip()
            if next_line != '' and next_line != '```':
                new_lines.append('```text')
            else:
                new_lines.append(line)
        else:
            # 这是结束标记，保持 ```
            new_lines.append(line)
    else:
        new_lines.append(line)
    
    i += 1

new_content = '\n'.join(new_lines)

# 确保所有结束标记都是 ```
new_content = re.sub(r'```text\n```', '```\n```', new_content)
new_content = re.sub(r'```text$', '```', new_content, flags=re.MULTILINE)

with open(file_path, 'w', encoding='utf-8') as f:
    f.write(new_content)

print("Fixed 08-二次型表示数问题.md")
