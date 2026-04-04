"""
语义搜索系统使用示例
"""
import asyncio
from typing import List


def example_embedding():
    """嵌入服务示例"""
    from embedding import get_embedding_service, LaTeXTokenizer
    
    # 获取嵌入服务
    embedding_service = get_embedding_service()
    
    # 示例文本
    text1 = "黎曼猜想是关于黎曼ζ函数零点分布的猜想。"
    text2 = "费马大定理指出：当整数 $n > 2$ 时，方程 $a^n + b^n = c^n$ 没有正整数解。"
    
    # 嵌入单个文本
    emb1 = embedding_service.embed_text(text1)
    print(f"文本1嵌入维度: {emb1.shape}")
    
    # 嵌入数学内容
    emb2 = embedding_service.embed_math_content(text2)
    print(f"文本2嵌入维度: {emb2.shape}")
    
    # 计算相似度
    similarity = embedding_service.compute_similarity(emb1, emb2)
    print(f"相似度: {similarity:.4f}")
    
    # LaTeX分词
    tokenizer = LaTeXTokenizer()
    tokens = tokenizer.tokenize(text2)
    print(f"\n分词结果:")
    print(f"  文本: {tokens['text']}")
    print(f"  公式: {tokens['latex']}")


def example_vector_store():
    """向量存储示例"""
    from vector_store import get_vector_store, VectorDocument
    
    # 获取向量存储
    store = get_vector_store("example")
    
    # 添加文档
    documents = [
        ("doc_001", "群论是研究代数结构群的数学分支。", {"branch": "代数"}),
        ("doc_002", "拓扑学研究空间在连续变形下保持不变的性质。", {"branch": "拓扑"}),
        ("doc_003", "微积分是研究变化率和累积量的数学分支。", {"branch": "分析"}),
    ]
    
    store.add_documents(documents)
    print(f"已索引 {len(documents)} 个文档")
    
    # 语义搜索
    results = store.search("代数结构", k=2)
    print("\n搜索结果:")
    for r in results:
        print(f"  [{r.rank}] {r.document.content[:30]}... (分数: {r.score:.4f})")
    
    # 保存索引
    store.save()
    print("\n索引已保存")


def example_hybrid_search():
    """混合搜索示例"""
    from hybrid_search import get_hybrid_search_service
    
    # 获取混合搜索服务
    search_service = get_hybrid_search_service()
    
    # 索引文档
    documents = [
        ("math_001", "费马大定理：当 $n > 2$ 时，$a^n + b^n = c^n$ 无正整数解。", {"type": "定理"}),
        ("math_002", "勾股定理：直角三角形中，$a^2 + b^2 = c^2$。", {"type": "定理"}),
        ("math_003", "欧拉公式：$e^{i\\pi} + 1 = 0$", {"type": "公式"}),
        ("math_004", "泰勒展开：$f(x) = \\sum_{n=0}^{\\infty} \\frac{f^{(n)}(a)}{n!}(x-a)^n$", {"type": "公式"}),
    ]
    
    search_service.index_documents(documents)
    print(f"已索引 {len(documents)} 个文档")
    
    # 混合搜索
    results = search_service.search("直角三角形边长关系", k=3)
    print("\n混合搜索结果:")
    for r in results:
        print(f"  [{r.rank}] {r.content[:40]}...")
        print(f"       语义: {r.semantic_score:.4f}, 关键词: {r.keyword_score:.4f}, 综合: {r.combined_score:.4f}")


def example_formula_search():
    """公式搜索示例"""
    from formula_search import get_formula_search_service
    
    # 获取公式搜索服务
    formula_service = get_formula_search_service()
    
    # 索引公式
    formulas = [
        ("f_001", "\\frac{a+b}{c}"),
        ("f_002", "\\frac{x+y}{z}"),
        ("f_003", "\\sum_{i=1}^{n} i = \\frac{n(n+1)}{2}"),
        ("f_004", "\\int_{a}^{b} f(x) dx"),
    ]
    
    for fid, latex in formulas:
        formula_service.index_formula(fid, latex)
    print(f"已索引 {len(formulas)} 个公式")
    
    # 搜索相似公式
    query = "\\frac{m+n}{p}"
    results = formula_service.search(query, k=3)
    
    print(f"\n查询公式: {query}")
    print("相似公式:")
    for r in results:
        print(f"  [{r.rank}] {r.formula_latex} (相似度: {r.similarity:.4f}, 类型: {r.match_type})")
    
    # 比较公式
    comparison = formula_service.compare_formulas("\\frac{a+b}{c}", "\\frac{x+y}{z}")
    print(f"\n公式比较:")
    print(f"  结构相似度: {comparison['structural_similarity']:.4f}")
    print(f"  是否等价: {comparison['is_equivalent']}")


def example_qa():
    """问答系统示例"""
    from qa_system import get_qa_system
    from hybrid_search import get_hybrid_search_service
    
    # 先索引一些文档
    search_service = get_hybrid_search_service()
    documents = [
        ("def_001", "黎曼猜想：黎曼ζ函数的所有非平凡零点的实部都是1/2。", {"type": "定义"}),
        ("def_002", "哥德巴赫猜想：每个大于2的偶数都可以表示为两个素数之和。", {"type": "定义"}),
        ("thm_001", "素数定理：π(x) ~ x/ln(x)，其中π(x)是不超过x的素数个数。", {"type": "定理"}),
    ]
    search_service.index_documents(documents)
    
    # 获取问答系统
    qa = get_qa_system()
    
    # 提问
    questions = [
        "什么是黎曼猜想？",
        "素数定理的内容是什么？",
    ]
    
    for q in questions:
        print(f"\n问题: {q}")
        answer = qa.ask(q)
        print(f"答案: {answer.text[:100]}...")
        print(f"置信度: {answer.confidence:.4f}")


def example_semantic_search():
    """完整语义搜索服务示例"""
    from semantic_search_service import get_semantic_search_service, SearchRequest
    
    # 获取语义搜索服务
    service = get_semantic_search_service()
    
    # 索引文档
    docs = [
        {
            "id": "concept_001",
            "content": "极限是微积分中的基本概念。函数 $f(x)$ 在 $x$ 趋近于 $a$ 时的极限记作 $\\lim_{x \\to a} f(x)$。",
            "metadata": {"branch": "分析", "level": "基础"}
        },
        {
            "id": "concept_002",
            "content": "导数描述了函数的变化率。函数 $f$ 在点 $a$ 的导数定义为 $f'(a) = \\lim_{h \\to 0} \\frac{f(a+h)-f(a)}{h}$。",
            "metadata": {"branch": "分析", "level": "基础"}
        },
        {
            "id": "concept_003",
            "content": "积分是微分的逆运算。定积分 $\\int_a^b f(x)dx$ 表示函数 $f$ 在区间 $[a,b]$ 上与x轴围成的有向面积。",
            "metadata": {"branch": "分析", "level": "基础"}
        },
    ]
    
    service.index_documents(docs)
    print(f"已索引 {len(docs)} 个文档")
    
    # 执行搜索
    request = SearchRequest(
        query="微积分基本定理",
        search_type="hybrid",
        k=5
    )
    
    response = service.search(request)
    print(f"\n搜索: {request.query}")
    print(f"找到 {response.total} 个结果，耗时 {response.query_time_ms:.2f}ms")
    
    for r in response.results:
        print(f"  [{r['rank']}] {r['content'][:50]}... (分数: {r['combined_score']:.4f})")
    
    # 问答
    print("\n问答示例:")
    answer = service.ask("什么是导数？")
    print(f"答案: {answer['answer'][:100]}...")
    print(f"置信度: {answer['confidence']:.4f}")
    
    # 保存索引
    service.save_index()
    print("\n索引已保存")


if __name__ == "__main__":
    print("=" * 60)
    print("FormalMath 语义搜索系统 - 使用示例")
    print("=" * 60)
    
    # 运行示例（取消注释需要运行的示例）
    
    # print("\n" + "=" * 40)
    # print("示例1: 嵌入服务")
    # print("=" * 40)
    # example_embedding()
    
    # print("\n" + "=" * 40)
    # print("示例2: 向量存储")
    # print("=" * 40)
    # example_vector_store()
    
    # print("\n" + "=" * 40)
    # print("示例3: 混合搜索")
    # print("=" * 40)
    # example_hybrid_search()
    
    # print("\n" + "=" * 40)
    # print("示例4: 公式搜索")
    # print("=" * 40)
    # example_formula_search()
    
    # print("\n" + "=" * 40)
    # print("示例5: 问答系统")
    # print("=" * 40)
    # example_qa()
    
    print("\n" + "=" * 40)
    print("示例6: 完整语义搜索服务")
    print("=" * 40)
    example_semantic_search()
