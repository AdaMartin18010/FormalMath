#!/usr/bin/env python3
"""
数据完整性修复工具
封装 data_integrity_checker_v2.py 的修复功能
"""

import sys
import subprocess
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent

def main():
    """运行数据完整性修复"""
    checker_path = PROJECT_ROOT / 'tools' / 'data_integrity_checker_v2.py'
    if checker_path.exists():
        result = subprocess.run([sys.executable, str(checker_path), '--fix'])
        return result.returncode
    else:
        print("错误: data_integrity_checker_v2.py 不存在")
        return 1

if __name__ == '__main__':
    sys.exit(main())
