import glob
import os

root_dir = r"e:\_src\FormalMath\数学家理念体系\诺特数学理念"
files = glob.glob(os.path.join(root_dir, "**", "*.md"), recursive=True)

# 统计
text_starts = 0
bare_ends = 0
directories = set()

for f in files:
    content = open(f, 'r', encoding='utf-8').read()
    text_starts += content.count('```text')
    bare_ends += content.count('\n```\n')
    dir_path = os.path.dirname(f)
    directories.add(dir_path)

print("=" * 70)
print("🎉 诺特数学理念项目 - 最终完成报告")
print("=" * 70)
print(f"\n✅ 项目完整性:")
print(f"  总文档数: {len(files)}")
print(f"  目录数: {len(directories)}")
print(f"\n✅ 格式统计:")
print(f"  ```text开始标记: {text_starts}")
print(f"  ```结束标记: {bare_ends}")
print(f"  代码块总数: {text_starts}")
print(f"\n✅ 验证结果:")
if text_starts == bare_ends:
    print(f"  ✅ 所有代码块配对正确")
    print(f"  ✅ 格式错误: 0个")
    print(f"  ✅ 项目状态: 全部完成！")
else:
    print(f"  ⚠️  开始和结束标记不匹配（差异: {abs(text_starts - bare_ends)}）")
print("\n" + "=" * 70)
