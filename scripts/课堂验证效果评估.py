#!/usr/bin/env python3
"""
FormalMath 课堂验证效果评估脚本
输入: 实验组与对照组的CSV数据
输出: 统计报告与显著性检验
"""

import sys
import pandas as pd
import numpy as np
from scipy import stats

def evaluate(exp_file, ctrl_file, output_file):
    exp = pd.read_csv(exp_file)
    ctrl = pd.read_csv(ctrl_file)
    
    metrics = ['pre_test', 'post_test_chapter', 'final_exam', 'satisfaction']
    report = []
    
    for m in metrics:
        e_mean = exp[m].mean()
        c_mean = ctrl[m].mean()
        e_std = exp[m].std()
        c_std = ctrl[m].std()
        t_stat, p_value = stats.ttest_ind(exp[m], ctrl[m])
        
        report.append({
            '指标': m,
            '实验组均值': round(e_mean, 2),
            '对照组均值': round(c_mean, 2),
            '提升幅度': round((e_mean - c_mean) / c_mean * 100, 2) if c_mean != 0 else 0,
            'p值': round(p_value, 4),
            '显著性': '***' if p_value < 0.001 else '**' if p_value < 0.01 else '*' if p_value < 0.05 else 'ns'
        })
    
    df = pd.DataFrame(report)
    df.to_csv(output_file, index=False, encoding='utf-8-sig')
    print(f"评估报告已保存: {output_file}")
    print(df.to_string(index=False))

if __name__ == '__main__':
    if len(sys.argv) < 4:
        print("用法: python 课堂验证效果评估.py <实验组.csv> <对照组.csv> <输出.csv>")
        sys.exit(1)
    evaluate(sys.argv[1], sys.argv[2], sys.argv[3])
