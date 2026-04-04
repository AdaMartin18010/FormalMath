"""
测试 Wikipedia 对齐模块
"""
import pytest
from unittest.mock import Mock, patch
import json


class TestWikipediaAlignment:
    """测试Wikipedia对齐功能"""
    
    def test_parse_wikipedia_response(self):
        """测试解析Wikipedia响应"""
        mock_response = {
            "query": {
                "pages": {
                    "12345": {
                        "pageid": 12345,
                        "title": "Group theory",
                        "extract": "In mathematics and abstract algebra..."
                    }
                }
            }
        }
        
        # 提取页面信息
        pages = mock_response.get("query", {}).get("pages", {})
        assert len(pages) == 1
        
        page = list(pages.values())[0]
        assert page["title"] == "Group theory"
        assert "extract" in page
    
    def test_extract_concept_from_wiki(self):
        """测试从Wikipedia提取概念"""
        wiki_content = """
        In mathematics, a group is a set equipped with an operation that 
        combines any two of its elements to form a third element.
        """
        
        # 模拟概念提取
        concept = {
            "name_en": "Group (mathematics)",
            "name_zh": "群",
            "category": "代数学",
            "description": wiki_content.strip()[:100] + "..."
        }
        
        assert concept["name_en"]
        assert concept["name_zh"]
        assert concept["category"]
    
    def test_calculate_similarity(self):
        """测试相似度计算"""
        def jaccard_similarity(set1, set2):
            intersection = len(set1.intersection(set2))
            union = len(set1.union(set2))
            return intersection / union if union > 0 else 0
        
        # 测试相同集合
        set1 = {"a", "b", "c"}
        set2 = {"a", "b", "c"}
        assert jaccard_similarity(set1, set2) == 1.0
        
        # 测试不同集合
        set3 = {"a", "b", "d"}
        similarity = jaccard_similarity(set1, set3)
        assert 0 < similarity < 1
        
        # 测试无交集
        set4 = {"x", "y", "z"}
        assert jaccard_similarity(set1, set4) == 0.0
    
    def test_match_concept_to_wiki(self):
        """测试匹配概念到Wikipedia"""
        local_concept = {
            "concept_id": "group_theory_001",
            "name": "群论",
            "category": "代数学"
        }
        
        wiki_pages = [
            {"title": "Group theory", "extract": "..."},
            {"title": "Ring theory", "extract": "..."},
            {"title": "Field theory", "extract": "..."}
        ]
        
        # 基于标题匹配
        matched = None
        for page in wiki_pages:
            if "group" in page["title"].lower():
                matched = page
                break
        
        assert matched is not None
        assert "group" in matched["title"].lower()


class TestMultilangAlignment:
    """测试多语言对齐"""
    
    def test_extract_multilang_titles(self):
        """测试提取多语言标题"""
        langlinks = {
            "en": "Group theory",
            "zh": "群论",
            "ja": "群論",
            "de": "Gruppentheorie",
            "fr": "Théorie des groupes"
        }
        
        assert len(langlinks) >= 3
        assert langlinks["en"] == "Group theory"
        assert langlinks["zh"] == "群论"
    
    def test_validate_translation(self):
        """测试验证翻译"""
        def validate_translation(original, translated, confidence_threshold=0.5):
            # 模拟验证逻辑
            if not original or not translated:
                return False
            
            # 检查长度比例
            length_ratio = len(translated) / len(original)
            return 0.1 < length_ratio < 10
        
        assert validate_translation("Group theory", "群论") is True
        assert validate_translation("", "群论") is False
        assert validate_translation("Group theory", "") is False
    
    def test_align_multilang_content(self):
        """测试对齐多语言内容"""
        contents = {
            "en": {"title": "Group theory", "content": "..."},
            "zh": {"title": "群论", "content": "..."},
            "ja": {"title": "群論", "content": "..."}
        }
        
        # 检查所有语言都有内容
        for lang in ["en", "zh", "ja"]:
            assert lang in contents
            assert "title" in contents[lang]
            assert "content" in contents[lang]


class TestDataValidation:
    """测试数据验证"""
    
    def test_validate_msc_code(self):
        """测试验证MSC编码"""
        valid_codes = ["20-XX", "20A05", "11N05", "14H52"]
        invalid_codes = ["ABC", "123", "20-"]
        
        def is_valid_msc(code):
            import re
            pattern = r'^\d{2}[A-Z](\d{2}|XX)$|^\d{2}-XX$'
            return bool(re.match(pattern, code))
        
        for code in valid_codes:
            assert is_valid_msc(code), f"{code} should be valid"
        
        for code in invalid_codes:
            assert not is_valid_msc(code), f"{code} should be invalid"
    
    def test_validate_concept_structure(self, sample_concept_data):
        """测试验证概念结构"""
        required_fields = ["concept_id", "name", "category"]
        
        for field in required_fields:
            assert field in sample_concept_data, f"Missing required field: {field}"
            assert sample_concept_data[field], f"Empty required field: {field}"
    
    def test_validate_url_format(self):
        """测试验证URL格式"""
        valid_urls = [
            "https://en.wikipedia.org/wiki/Group_theory",
            "https://zh.wikipedia.org/wiki/群论",
            "https://mathworld.wolfram.com/Group.html"
        ]
        invalid_urls = [
            "not-a-url",
            "ftp://example.com",
            ""
        ]
        
        def is_valid_url(url):
            return url.startswith('https://') and ('wikipedia.org' in url or 'wolfram.com' in url)
        
        for url in valid_urls:
            assert is_valid_url(url), f"{url} should be valid"
        
        for url in invalid_urls:
            assert not is_valid_url(url), f"{url} should be invalid"
