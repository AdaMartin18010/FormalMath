#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 概念图谱扩展脚本 - 第十二批
将概念图谱从100个扩展到200个概念
"""

import yaml
from datetime import datetime

def load_existing_concepts(filepath):
    """加载现有概念数据"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    return content

def create_new_concepts():
    """创建新增的100个概念（5个分支各20个）"""
    
    # 概率统计 - 20个概念
    probability_statistics = [
        {
            "concept_id": "probability_measure",
            "name": "概率测度",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "measure_theory", "level": "L3", "relation": "依赖"},
                {"concept_id": "sigma_algebra", "level": "L2", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "random_variable", "level": "L2", "relation": "被依赖"},
                {"concept_id": "conditional_probability", "level": "L2", "relation": "被依赖"},
                {"concept_id": "expectation", "level": "L2", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 25
        },
        {
            "concept_id": "random_variable",
            "name": "随机变量",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "probability_measure", "level": "L3", "relation": "依赖"},
                {"concept_id": "measurable_function", "level": "L2", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "probability_distribution", "level": "L2", "relation": "被依赖"},
                {"concept_id": "expectation", "level": "L2", "relation": "被依赖"},
                {"concept_id": "stochastic_process", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 2,
            "estimated_hours": 20
        },
        {
            "concept_id": "probability_distribution",
            "name": "概率分布",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "random_variable", "level": "L2", "relation": "依赖"},
                {"concept_id": "lebesgue_integral", "level": "L3", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "normal_distribution", "level": "L2", "relation": "被依赖"},
                {"concept_id": "central_limit_theorem", "level": "L3", "relation": "被依赖"},
                {"concept_id": "statistical_inference", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 2,
            "estimated_hours": 18
        },
        {
            "concept_id": "expectation",
            "name": "期望",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "random_variable", "level": "L2", "relation": "依赖"},
                {"concept_id": "lebesgue_integral", "level": "L3", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "variance", "level": "L2", "relation": "被依赖"},
                {"concept_id": "covariance", "level": "L2", "relation": "被依赖"},
                {"concept_id": "moment_generating_function", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 2,
            "estimated_hours": 15
        },
        {
            "concept_id": "conditional_probability",
            "name": "条件概率",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "probability_measure", "level": "L3", "relation": "依赖"},
                {"concept_id": "random_variable", "level": "L2", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "bayes_theorem", "level": "L2", "relation": "被依赖"},
                {"concept_id": "conditional_expectation", "level": "L3", "relation": "被依赖"},
                {"concept_id": "markov_property", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 2,
            "estimated_hours": 15
        },
        {
            "concept_id": "bayes_theorem",
            "name": "贝叶斯定理",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "conditional_probability", "level": "L2", "relation": "依赖"},
                {"concept_id": "probability_distribution", "level": "L2", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "bayesian_inference", "level": "L3", "relation": "被依赖"},
                {"concept_id": "posterior_distribution", "level": "L3", "relation": "被依赖"},
                {"concept_id": "belief_network", "level": "L4", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 20
        },
        {
            "concept_id": "stochastic_process",
            "name": "随机过程",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "random_variable", "level": "L2", "relation": "依赖"},
                {"concept_id": "probability_measure", "level": "L3", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "markov_chain", "level": "L3", "relation": "被依赖"},
                {"concept_id": "martingale", "level": "L3", "relation": "被依赖"},
                {"concept_id": "brownian_motion", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 35
        },
        {
            "concept_id": "markov_chain",
            "name": "马尔可夫链",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "stochastic_process", "level": "L3", "relation": "依赖"},
                {"concept_id": "markov_property", "level": "L3", "relation": "依赖"},
                {"concept_id": "transition_matrix", "level": "L2", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "markov_chain_monte_carlo", "level": "L4", "relation": "被依赖"},
                {"concept_id": "hidden_markov_model", "level": "L4", "relation": "被依赖"},
                {"concept_id": "markov_decision_process", "level": "L4", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 30
        },
        {
            "concept_id": "martingale",
            "name": "鞅",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "stochastic_process", "level": "L3", "relation": "依赖"},
                {"concept_id": "conditional_expectation", "level": "L3", "relation": "依赖"},
                {"concept_id": "filtration", "level": "L3", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "martingale_convergence", "level": "L4", "relation": "被依赖"},
                {"concept_id": "stochastic_integral", "level": "L4", "relation": "被依赖"}
            ],
            "difficulty": 4,
            "estimated_hours": 40
        },
        {
            "concept_id": "brownian_motion",
            "name": "布朗运动",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "stochastic_process", "level": "L3", "relation": "依赖"},
                {"concept_id": "normal_distribution", "level": "L2", "relation": "依赖"},
                {"concept_id": "continuity", "level": "L1", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "stochastic_calculus", "level": "L4", "relation": "被依赖"},
                {"concept_id": "ito_calculus", "level": "L4", "relation": "被依赖"}
            ],
            "difficulty": 4,
            "estimated_hours": 35
        },
        {
            "concept_id": "law_of_large_numbers",
            "name": "大数定律",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "expectation", "level": "L2", "relation": "依赖"},
                {"concept_id": "variance", "level": "L2", "relation": "依赖"},
                {"concept_id": "limit", "level": "L1", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "convergence_in_probability", "level": "L3", "relation": "被依赖"},
                {"concept_id": "monte_carlo_method", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 20
        },
        {
            "concept_id": "central_limit_theorem",
            "name": "中心极限定理",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "probability_distribution", "level": "L2", "relation": "依赖"},
                {"concept_id": "variance", "level": "L2", "relation": "依赖"},
                {"concept_id": "characteristic_function", "level": "L3", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "normal_approximation", "level": "L3", "relation": "被依赖"},
                {"concept_id": "confidence_interval", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 25
        },
        {
            "concept_id": "statistical_inference",
            "name": "统计推断",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "probability_distribution", "level": "L2", "relation": "依赖"},
                {"concept_id": "sampling_distribution", "level": "L2", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "parameter_estimation", "level": "L3", "relation": "被依赖"},
                {"concept_id": "hypothesis_testing", "level": "L3", "relation": "被依赖"},
                {"concept_id": "bayesian_inference", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 30
        },
        {
            "concept_id": "parameter_estimation",
            "name": "参数估计",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "statistical_inference", "level": "L3", "relation": "依赖"},
                {"concept_id": "likelihood_function", "level": "L3", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "maximum_likelihood", "level": "L3", "relation": "被依赖"},
                {"concept_id": "confidence_interval", "level": "L3", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 25
        },
        {
            "concept_id": "hypothesis_testing",
            "name": "假设检验",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "statistical_inference", "level": "L3", "relation": "依赖"},
                {"concept_id": "sampling_distribution", "level": "L2", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "type_error", "level": "L3", "relation": "被依赖"},
                {"concept_id": "p_value", "level": "L3", "relation": "被依赖"},
                {"concept_id": "power_analysis", "level": "L4", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 25
        },
        {
            "concept_id": "regression_analysis",
            "name": "回归分析",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "statistical_inference", "level": "L3", "relation": "依赖"},
                {"concept_id": "linear_algebra", "level": "L2", "relation": "依赖"},
                {"concept_id": "variance", "level": "L2", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "linear_regression", "level": "L3", "relation": "被依赖"},
                {"concept_id": "logistic_regression", "level": "L3", "relation": "被依赖"},
                {"concept_id": "time_series_analysis", "level": "L4", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 30
        },
        {
            "concept_id": "bayesian_inference",
            "name": "贝叶斯推断",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "bayes_theorem", "level": "L2", "relation": "依赖"},
                {"concept_id": "statistical_inference", "level": "L3", "relation": "依赖"},
                {"concept_id": "prior_distribution", "level": "L3", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "posterior_distribution", "level": "L3", "relation": "被依赖"},
                {"concept_id": "credible_interval", "level": "L3", "relation": "被依赖"},
                {"concept_id": "markov_chain_monte_carlo", "level": "L4", "relation": "被依赖"}
            ],
            "difficulty": 3,
            "estimated_hours": 35
        },
        {
            "concept_id": "time_series_analysis",
            "name": "时间序列分析",
            "category": "概率统计",
            "prerequisites": [
                {"concept_id": "regression_analysis", "level": "L3", "relation": "依赖"},
                {"concept_id": "stochastic_process", "level": "L3", "relation": "依赖"},
                {"concept_id": "autocorrelation", "level": "L3", "relation": "依赖"}
            ],
            "successors": [
                {"concept_id": "arima_model", "level": "L4", "relation": "被依赖"},
                {"concept_id": "forecasting", "level": "L4", "relation": "被依赖"}
            ],
            "difficulty": 4,
            "estimated_hours": 40
        }
    ]
    
    return probability_statistics

def main():
    # 创建输出文件
    output_file = 'project/concept_prerequisites_extended.yaml'
    
    # 加载现有内容
    existing_content = load_existing_concepts('project/concept_prerequisites.yaml')
    
    # 获取新概念
    new_concepts = create_new_concepts()
    
    print(f"创建了 {len(new_concepts)} 个概率统计概念")
    print(f"新概念示例: {new_concepts[0]['name']} ({new_concepts[0]['concept_id']})")
    
    # 保存为YAML格式
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write("# FormalMath 扩展概念数据\n")
        f.write("# 第十二批：概率统计概念\n\n")
        yaml.dump({'new_concepts': new_concepts}, f, allow_unicode=True, sort_keys=False)
    
    print(f"已保存到: {output_file}")

if __name__ == '__main__':
    main()
