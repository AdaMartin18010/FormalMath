# -*- coding: utf-8 -*-
with open('temp_scripts/write_18100a.py', 'r', encoding='utf-8') as f:
    code = f.read()

print('File length:', len(code))

# Search for the content markers
idx1 = code.find("r'''")
idx2 = code.rfind("'''")

print('First r triple-single at:', idx1)
print('Last triple-single at:', idx2)

if idx1 >= 0:
    print('Around r:', repr(code[idx1:idx1+10]))
if idx2 >= 0:
    print('Around triple:', repr(code[idx2-5:idx2+5]))

if idx1 >= 0 and idx2 > idx1 + 3:
    md = code[idx1+4:idx2]
    print('Extracted md length:', len(md))
    out_path = 'project/adaptive-learning-system/validation/测试题库-MIT-18.100A.md'
    with open(out_path, 'w', encoding='utf-8') as f2:
        f2.write(md)
    print('Written to:', out_path)
else:
    print('Failed to find markers')
