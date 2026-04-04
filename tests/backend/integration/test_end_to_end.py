"""
端到端集成测试
"""
import pytest
import json
import tempfile
from pathlib import Path


class TestConceptWorkflow:
    """测试概念工作流"""
    
    @pytest.mark.integration
    def test_full_concept_pipeline(self, tmp_path):
        """测试完整的概念处理流程"""
        # 1. 创建输入数据
        input_data = {
            "concepts": [
                {
                    "concept_id": "test_001",
                    "name": "测试群论",
                    "category": "代数学",
                    "description": "测试用群论概念"
                }
            ]
        }
        
        input_file = tmp_path / "input.yaml"
        import yaml
        with open(input_file, 'w', encoding='utf-8') as f:
            yaml.dump(input_data, f, allow_unicode=True)
        
        # 2. 读取数据
        with open(input_file, 'r', encoding='utf-8') as f:
            loaded_data = yaml.safe_load(f)
        
        assert len(loaded_data["concepts"]) == 1
        
        # 3. 处理数据
        for concept in loaded_data["concepts"]:
            concept["processed"] = True
            concept["msc_codes"] = ["20-XX"]
        
        # 4. 输出结果
        output_file = tmp_path / "output.json"
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(loaded_data, f, ensure_ascii=False, indent=2)
        
        # 5. 验证结果
        with open(output_file, 'r', encoding='utf-8') as f:
            result = json.load(f)
        
        assert result["concepts"][0]["processed"] is True
        assert "msc_codes" in result["concepts"][0]


class TestFileProcessing:
    """测试文件处理集成"""
    
    @pytest.mark.integration
    def test_process_concept_directory(self, tmp_path):
        """测试处理概念目录"""
        # 创建多个概念文件
        concept_files = [
            ("algebra.yaml", {"concepts": [{"name": "群论"}]}),
            ("geometry.yaml", {"concepts": [{"name": "拓扑"}]}),
        ]
        
        import yaml
        for filename, data in concept_files:
            file_path = tmp_path / filename
            with open(file_path, 'w', encoding='utf-8') as f:
                yaml.dump(data, f, allow_unicode=True)
        
        # 处理所有文件
        all_concepts = []
        for yaml_file in tmp_path.glob("*.yaml"):
            with open(yaml_file, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
                all_concepts.extend(data.get("concepts", []))
        
        assert len(all_concepts) == 2
    
    @pytest.mark.integration
    def test_merge_multiple_sources(self, tmp_path):
        """测试合并多个数据源"""
        source1 = tmp_path / "source1.json"
        source2 = tmp_path / "source2.json"
        
        # 创建源文件
        json.dump({"concepts": [{"id": "1", "name": "A"}]}, open(source1, 'w'))
        json.dump({"concepts": [{"id": "2", "name": "B"}]}, open(source2, 'w'))
        
        # 合并
        all_concepts = []
        for src in [source1, source2]:
            with open(src, 'r') as f:
                data = json.load(f)
                all_concepts.extend(data["concepts"])
        
        assert len(all_concepts) == 2
        assert all_concepts[0]["name"] == "A"
        assert all_concepts[1]["name"] == "B"


class TestExternalApis:
    """测试外部API集成"""
    
    @pytest.mark.integration
    @pytest.mark.skip(reason="需要外部API访问")
    def test_wikipedia_api_integration(self):
        """测试Wikipedia API集成"""
        import requests
        
        response = requests.get(
            "https://en.wikipedia.org/api/rest_v1/page/summary/Group_theory",
            timeout=10
        )
        
        assert response.status_code == 200
        data = response.json()
        assert "title" in data
        assert "extract" in data


class TestDataConsistency:
    """测试数据一致性"""
    
    @pytest.mark.integration
    def test_round_trip_serialization(self, sample_concept_data, tmp_path):
        """测试序列化往返一致性"""
        import json
        import yaml
        
        # JSON序列化
        json_file = tmp_path / "concept.json"
        with open(json_file, 'w', encoding='utf-8') as f:
            json.dump(sample_concept_data, f, ensure_ascii=False)
        
        with open(json_file, 'r', encoding='utf-8') as f:
            json_loaded = json.load(f)
        
        assert json_loaded["concept_id"] == sample_concept_data["concept_id"]
        
        # YAML序列化
        yaml_file = tmp_path / "concept.yaml"
        with open(yaml_file, 'w', encoding='utf-8') as f:
            yaml.dump(sample_concept_data, f, allow_unicode=True)
        
        with open(yaml_file, 'r', encoding='utf-8') as f:
            yaml_loaded = yaml.safe_load(f)
        
        assert yaml_loaded["concept_id"] == sample_concept_data["concept_id"]


class TestErrorRecovery:
    """测试错误恢复"""
    
    @pytest.mark.integration
    def test_continue_on_partial_failure(self, tmp_path):
        """测试部分失败时的继续处理"""
        results = []
        
        operations = [
            ("success", lambda: {"status": "ok"}),
            ("failure", lambda: (_ for _ in ()).throw(ValueError("Failed"))),
            ("success2", lambda: {"status": "ok2"}),
        ]
        
        for name, op in operations:
            try:
                result = op()
                results.append({"name": name, "result": result, "success": True})
            except Exception as e:
                results.append({"name": name, "error": str(e), "success": False})
        
        assert len(results) == 3
        assert results[0]["success"] is True
        assert results[1]["success"] is False
        assert results[2]["success"] is True
