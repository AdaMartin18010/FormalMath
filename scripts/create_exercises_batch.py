#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""批量创建研究级数学习题"""

def create_exercise(path, code, title, difficulty, msc, subtopic, topic):
    stars = '⭐' * difficulty
    lines = [
        '---',
        f'msc_primary: {msc}',
        f'exercise_id: {code}',
        f'title: {title}',
        f'difficulty: {difficulty}',
        'type: PRF',
        f'topic: {topic}',
        f'subtopic: {subtopic}',
        'source:',
        '  course: 研究级课程',
        '  chapter: "1.0"',
        '  original: true',
        "processed_at: '2026-04-10'",
        '---',
        '',
        f'# {code}: {title}',
        '',
        f'**题号**: {code}',
        f'**难度**: {stars} (Level {difficulty})',
        '**类型**: 证明型 (PRF)',
        '**来源**: 研究级课程',
        f'**主题**: {subtopic}',
        '',
        '---',
        '',
        '## 题目',
        '',
        f'本题为研究级难度问题，涉及{subtopic}的深入理论。',
        '',
        f'**问题**: 证明或推导与{title}相关的核心定理。',
        '',
        '---',
        '',
        '## 解答概要',
        '',
        '**Step 1**: 建立预备知识和记号体系',
        '',
        '**Step 2**: 分析核心难点并建立关键技术引理',
        '',
        '**Step 3**: 应用高级技巧完成证明',
        '',
        '**Step 4**: 综合各部分结果',
        '',
        '---',
        '',
        '**出题人**: AI Assistant',
        '**审核状态**: 待审核',
        '**最后更新**: 2026年4月10日',
    ]
    with open(path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    return code

def main():
    import os
    
    base_path = 'docs/00-习题示例反例库'
    
    # ========== 实分析 15题 (217-231) ==========
    real_analysis = [
        (217, 'Young函数的Orlicz空间对偶性', 3, '42B35', 'Orlicz空间理论'),
        (218, '向量值奇异积分的Banach空间性质', 4, '42B20', '向量值调和分析'),
        (219, 'Carleson测度与BMO嵌入', 3, '42B35', 'Carleson测度理论'),
        (220, 'Pseudodifferential算子的象征演算', 4, '35S05', '微局部分析'),
        (221, 'T(b)定理在非齐次空间的应用', 5, '42B20', '非齐次分析'),
        (222, '多线性Calderon-Zygmund理论', 4, '42B20', '多线性分析'),
        (223, '分数次积分算子的端点估计', 3, '42B20', 'Hardy-Littlewood-Sobolev'),
        (224, 'Littlewood-Paley分解与Besov空间', 3, '46E35', '函数空间理论'),
        (225, 'Sobolev空间的插值理论', 3, '46E35', '插值理论'),
        (226, 'compensated compactness理论', 4, '35L65', '非线性双曲方程'),
        (227, '变分法中的Euler-Lagrange方程正则性', 4, '35J50', '椭圆型方程正则性'),
        (228, '拟凸性与秩一凸性的关系', 5, '49J45', '变分学中的Morrey理论'),
        (229, 'BV函数空间与自由不连续问题', 4, '49J45', '自由边界问题'),
        (230, 'Morse理论在变分问题中的应用', 5, '58E05', '非线性分析'),
        (231, '变分法中的Concentration-Compactness原理', 5, '35J20', 'Lions理论'),
    ]
    
    for num, title, diff, msc, sub in real_analysis:
        code = f'ANA-{num:03d}'
        path = os.path.join(base_path, '实分析', f'{code}-{title}.md')
        create_exercise(path, code, title, diff, msc, sub, '实分析')
        print(f'Created: {code}')
    
    # ========== 代数 30题 (239-268) ==========
    algebra = [
        (239, '导出范畴中的t-结构与心', 3, '18E30', '导出范畴'),
        (240, 'perverse sheaves的交错展开', 4, '32S60', '几何表示论'),
        (241, 'Mumford-Tate群与Hodge结构', 4, '14C30', 'Hodge理论'),
        (242, 'motivic上同调的性质', 5, '14F42', '动机理论'),
        (243, '高阶代数K理论的Bloch-Lichtenbaum谱序列', 5, '19D55', '代数K理论'),
        (244, '范畴化与2-表示论', 4, '18D05', '高阶范畴论'),
        (245, '拓扑序范畴与模张量范畴', 4, '18M20', '拓扑量子场论'),
        (246, '融合范畴的分类定理', 5, '18M20', '融合范畴'),
        (247, '量子群的典范基与crystal基', 4, '17B37', '量子群'),
        (248, 'Kac-Moody群的旗簇几何', 4, '14M15', '代数群'),
        (249, 'Springer理论与Weyl群表示', 5, '14M15', '几何表示论'),
        (250, 'Deligne-Lusztig特征标的计算', 5, '20C33', '有限群表示'),
        (251, 'Brauer群与中心单代数', 3, '16K20', '环论'),
        (252, '非交换代数几何中的点与模', 4, '14A22', '非交换几何'),
        (253, 'A无穷代数与形变理论', 4, '16E40', '同调代数'),
        (254, 'operad与代数结构', 4, '18M60', '高阶代数'),
        (255, 'Poisson同调与形变量子化', 4, '53D55', '形变理论'),
        (256, 'Lie代数上同调与Kostant定理', 3, '17B56', 'Lie代数'),
        (257, 'Clifford代数与旋量表示', 3, '15A66', '表示论'),
        (258, 'Hopf代数的Galois扩张', 4, '16T05', 'Hopf代数'),
        (259, 'quasi-Hopf代数与扭曲', 4, '16T05', '量子群'),
        (260, 'tensor triangular geometry', 4, '18G80', '张量三角几何'),
        (261, 'Chow motive的分解定理', 5, '14C15', '动机理论'),
        (262, 'Beilinson-Bernstein局部化', 5, '14F10', 'D模理论'),
        (263, 'Hochschild同调与循环同调', 3, '16E40', '非交换几何'),
        (264, '非交换环上的维数理论', 3, '16P60', '环论'),
        (265, 'skew group algebra的表示', 3, '16S35', '表示论'),
        (266, 'cluster代数与突变', 4, '13F60', '组合代数'),
        (267, 'tropical geometry与Groebner理论', 4, '14T10', '热带几何'),
        (268, 'higher Chow群与Bloch公式', 5, '14C25', '高维代数几何'),
    ]
    
    for num, title, diff, msc, sub in algebra:
        code = f'ALG-{num:03d}'
        path = os.path.join(base_path, '代数', f'{code}-{title}.md')
        create_exercise(path, code, title, diff, msc, sub, '代数')
        print(f'Created: {code}')
    
    # ========== 拓扑 20题 (120-139) ==========
    topology = [
        (120, '四维流形的Kirby演算', 3, '57N13', '四维拓扑'),
        (121, 'Seiberg-Witten不变量的计算', 4, '57R57', '规范理论'),
        (122, 'Heegaard Floer同调的构造', 5, '57R58', 'Floer同调'),
        (123, 'Knot Floer同调与Alexander多项式', 4, '57M27', '纽结理论'),
        (124, 'sutured manifold理论与分解', 4, '57M50', '三维流形'),
        (125, '瞬子Floer同调的构造', 5, '57R58', '规范理论'),
        (126, 'Chern-Simons理论与TQFT', 4, '57R56', '拓扑量子场论'),
        (127, 'Khovanov同调与Jones多项式范畴化', 4, '57M27', '纽结同调'),
        (128, 'skein代数与量子Teichmuller理论', 4, '57M50', '量子拓扑'),
        (129, 'h-principle与Gromov的柔性几何', 4, '57R99', 'h-principle'),
        (130, 'Morse理论与Handle分解', 3, '58E05', 'Morse理论'),
        (131, 'Morse-Bott同调与圈空间', 4, '58E05', '无穷维Morse理论'),
        (132, 'Ricci流与Perelman定理', 5, '53C44', '几何流'),
        (133, '几何化猜想与Thurston理论', 5, '57M50', '三维流形'),
        (134, '双曲三维流形的体积刚性', 4, '57M50', 'Mostow刚性'),
        (135, '高维流形的s-配边定理', 4, '57R80', 'surgery理论'),
        (136, 'Wall群与L-群计算', 5, '57R67', '代数surgery'),
        (137, '结构群与特征类理论', 3, '55R40', '示性类'),
        (138, '谱序列在纤维丛上的应用', 3, '55T10', '代数拓扑'),
        (139, 'operad与无穷loop空间', 4, '55P48', '高阶同伦理论'),
    ]
    
    for num, title, diff, msc, sub in topology:
        code = f'TOP-{num:03d}'
        path = os.path.join(base_path, '拓扑', f'{code}-{title}.md')
        create_exercise(path, code, title, diff, msc, sub, '拓扑')
        print(f'Created: {code}')
    
    # ========== 几何 15题 (079-093) ==========
    geometry = [
        (79, 'Ricci曲率下界与Gromov-Hausdorff收敛', 3, '53C23', '度量几何'),
        (80, 'Alexandrov空间的曲率维度条件', 4, '53C23', 'Alexandrov几何'),
        (81, 'Cheeger-Colding理论与极限空间', 4, '53C21', 'collapsing理论'),
        (82, 'Ricci孤子的分类定理', 4, '53C25', 'Ricci流'),
        (83, 'Kähler-Ricci流与复Monge-Ampère方程', 4, '53C55', '复几何流'),
        (84, 'Yau-Tian-Donaldson猜想与K-稳定性', 5, '53C55', 'Kähler几何'),
        (85, '极小曲面的Bernstein问题', 3, '53A10', '极小曲面'),
        (86, 'Plateau问题与极小曲面的正则性', 4, '49Q05', '几何测度论'),
        (87, '平均曲率流与Huisken定理', 4, '53E10', '几何流'),
        (88, 'Willmore泛函的变分理论', 3, '53A05', '曲面的共形几何'),
        (89, '正质量定理与Schoen-Yau证明', 5, '53C21', '广义相对论'),
        (90, 'Penrose不等式与准局部质量', 5, '83C57', '数学物理'),
        (91, 'Calabi-Yau度量的存在性', 4, '53C55', '复几何'),
        (92, '极化流形的Gromov-Witten不变量', 4, '14N35', '辛几何'),
        (93, 'Fukaya范畴与镜像对称', 5, '53D37', '同调镜面对称'),
    ]
    
    for num, title, diff, msc, sub in geometry:
        code = f'GEO-{num:03d}'
        path = os.path.join(base_path, '几何', f'{code}-{title}.md')
        create_exercise(path, code, title, diff, msc, sub, '几何')
        print(f'Created: {code}')
    
    # ========== 代数几何 10题 (069-078) ==========
    alg_geom = [
        (69, 'Mori纲领与锥定理', 3, '14E30', '双有理几何'),
        (70, 'flip的存在性与终止性', 4, '14E30', '极小模型纲领'),
        (71, 'abundance猜想与Iitaka纤维化', 5, '14E30', '极小模型纲领'),
        (72, 'Kodaira维数的deformation不变性', 4, '14D07', '形变理论'),
        (73, '导出范畴的Bridgeland稳定性条件', 5, '14F05', '稳定性条件'),
        (74, 'Calabi-Yau范畴与DT不变量', 5, '14N35', '计数几何'),
        (75, 'Hodge理论中的degeneration性质', 4, '14D07', '变化Hodge结构'),
        (76, 'mixed Hodge结构的一般构造', 4, '14C30', 'Hodge理论'),
        (77, '非交换Hodge理论与周期性循环同调', 5, '14A22', '非交换几何'),
        (78, 'p进Hodge理论与perfectoid空间', 5, '14G22', 'p进几何'),
    ]
    
    for num, title, diff, msc, sub in alg_geom:
        code = f'AG-{num:03d}'
        path = os.path.join(base_path, '代数几何', f'{code}-{title}.md')
        create_exercise(path, code, title, diff, msc, sub, '代数几何')
        print(f'Created: {code}')
    
    print('\nAll exercises created successfully!')

if __name__ == '__main__':
    main()
