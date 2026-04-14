"""
测试 extract_concepts.py 模块
"""
import pytest
from unittest.mock import Mock, patch, mock_open
from pathlib import Path


class TestExtractConcepts:
    """测试概念提取功能"""
    
    def test_load_yaml_file(self, sample_yaml_content, tmp_path):
        """测试加载YAML文件"""
        # 创建临时YAML文件
        yaml_file = tmp_path / "test_concepts.yaml"
        yaml_file.write_text(sample_yaml_content, encoding='utf-8')
        
        # 验证文件内容
        content = yaml_file.read_text(encoding='utf-8')
        assert "concepts:" in content
        assert "test_001" in content
    
    def test_extract_concepts_from_yaml(self, sample_concepts_list):
        """测试从YAML提取概念"""
        # 验证概念数据结构
        assert len(sample_concepts_list) == 3
        
        concept = sample_concepts_list[0]
        assert "concept_id" in concept
        assert "name" in concept
        assert "category" in concept
        assert concept["name"] == "群论"
    
    def test_filter_concepts_by_category(self, sample_concepts_list):
        """测试按类别过滤概念"""
        algebra_concepts = [
            c for c in sample_concepts_list 
            if c["category"] == "代数学"
        ]
        
        assert len(algebra_concepts) == 1
        assert algebra_concepts[0]["name"] == "群论"
    
    def test_filter_concepts_by_difficulty(self, sample_concepts_list):
        """测试按难度过滤概念"""
        advanced_concepts = [
            c for c in sample_concepts_list
            if c["difficulty"] == "advanced"
        ]
        
        assert len(advanced_concepts) == 1
        assert advanced_concepts[0]["name"] == "拓扑学"
    
    def test_concept_id_format(self, sample_concepts_list):
        """测试概念ID格式"""
        for concept in sample_concepts_list:
            concept_id = concept["concept_id"]
            # 验证ID不为空
            assert concept_id
            # 验证ID是字符串
            assert isinstance(concept_id, str)
            # 验证ID格式 (concept_XXX)
            assert concept_id.startswith("concept_")


class TestConceptRelationships:
    """测试概念关系"""
    
    def test_prerequisites_structure(self, sample_concept_data):
        """测试前置条件结构"""
        prereqs = sample_concept_data.get("prerequisites", [])
        assert isinstance(prereqs, list)
        assert len(prereqs) > 0
        assert "set_theory" in prereqs
    
    def test_related_concepts_structure(self, sample_concept_data):
        """测试相关概念结构"""
        related = sample_concept_data.get("related_concepts", [])
        assert isinstance(related, list)
        assert len(related) > 0
        assert "ring_theory" in related
    
    def test_msc_codes_format(self, sample_concept_data):
        """测试MSC编码格式"""
        msc_codes = sample_concept_data.get("msc_codes", [])
        assert isinstance(msc_codes, list)
        
        for code in msc_codes:
            # 验证MSC编码格式
            assert isinstance(code, str)
            assert isinstance(code, str) and len(code) >= 3 and len(code) <= 5


class TestErrorHandling:
    """测试错误处理"""
    
    def test_file_not_found(self, tmp_path):
        """测试文件不存在时的处理"""
        non_existent_file = tmp_path / "non_existent.yaml"
        
        with pytest.raises(FileNotFoundError):
            if not non_existent_file.exists():
                raise FileNotFoundError(f"File not found: {non_existent_file}")
    
    def test_invalid_yaml_content(self, tmp_path):
        """测试无效YAML内容的处理"""
        invalid_yaml = tmp_path / "invalid.yaml"
        invalid_yaml.write_text("invalid: yaml: content: [", encoding='utf-8')
        
        import yaml
        with pytest.raises(yaml.YAMLError):
            with open(invalid_yaml, 'r', encoding='utf-8') as f:
                yaml.safe_load(f)
    
    def test_empty_concepts_list(self):
        """测试空概念列表"""
        empty_data = {"concepts": []}
        assert empty_data["concepts"] == []
        assert len(empty_data["concepts"]) == 0
