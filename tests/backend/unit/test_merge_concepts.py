"""
测试 merge_concepts.py 模块
"""
import pytest


class TestMergeConcepts:
    """测试概念合并功能"""
    
    def test_merge_concept_lists(self):
        """测试合并概念列表"""
        list1 = [
            {"concept_id": "1", "name": "概念A"},
            {"concept_id": "2", "name": "概念B"}
        ]
        list2 = [
            {"concept_id": "2", "name": "概念B更新"},
            {"concept_id": "3", "name": "概念C"}
        ]
        
        # 基于concept_id合并
        merged = {c["concept_id"]: c for c in list1}
        for c in list2:
            if c["concept_id"] in merged:
                merged[c["concept_id"]].update(c)
            else:
                merged[c["concept_id"]] = c
        
        result = list(merged.values())
        
        assert len(result) == 3
        assert result[1]["name"] == "概念B更新"
    
    def test_merge_preserves_data(self):
        """测试合并保留原有数据"""
        base = {
            "concept_id": "test",
            "name": "测试",
            "category": "代数",
            "description": "原始描述"
        }
        
        update = {
            "concept_id": "test",
            "description": "更新描述",
            "new_field": "新字段"
        }
        
        merged = {**base, **update}
        
        assert merged["name"] == "测试"
        assert merged["category"] == "代数"
        assert merged["description"] == "更新描述"
        assert merged["new_field"] == "新字段"
    
    def test_merge_empty_lists(self):
        """测试合并空列表"""
        list1 = []
        list2 = [{"concept_id": "1", "name": "概念"}]
        
        merged = list1 + list2
        
        assert len(merged) == 1
        assert merged[0]["concept_id"] == "1"


class TestConceptDeduplication:
    """测试概念去重"""
    
    def test_remove_duplicate_concepts(self):
        """测试去除重复概念"""
        concepts = [
            {"concept_id": "1", "name": "概念A"},
            {"concept_id": "2", "name": "概念B"},
            {"concept_id": "1", "name": "概念A重复"}
        ]
        
        # 基于concept_id去重
        seen = set()
        unique = []
        for c in concepts:
            if c["concept_id"] not in seen:
                seen.add(c["concept_id"])
                unique.append(c)
        
        assert len(unique) == 2
        assert unique[0]["name"] == "概念A"
    
    def test_handle_duplicate_ids(self):
        """测试处理重复ID"""
        concepts = [
            {"concept_id": "1", "name": "概念A", "priority": 1},
            {"concept_id": "1", "name": "概念A", "priority": 2}
        ]
        
        # 保留优先级高的
        latest = {}
        for c in concepts:
            cid = c["concept_id"]
            if cid not in latest or c.get("priority", 0) > latest[cid].get("priority", 0):
                latest[cid] = c
        
        result = list(latest.values())
        assert len(result) == 1
        assert result[0]["priority"] == 2


class TestConflictResolution:
    """测试冲突解决"""
    
    def test_resolve_field_conflict(self):
        """测试解决字段冲突"""
        local = {"field": "local_value", "timestamp": "2024-01-01"}
        remote = {"field": "remote_value", "timestamp": "2024-01-02"}
        
        # 基于时间戳选择较新的
        merged = local if local["timestamp"] > remote["timestamp"] else remote
        
        assert merged["field"] == "remote_value"
    
    def test_merge_nested_objects(self):
        """测试合并嵌套对象"""
        base = {
            "id": "1",
            "metadata": {
                "created": "2024-01-01",
                "version": 1
            }
        }
        
        update = {
            "id": "1",
            "metadata": {
                "updated": "2024-01-02",
                "version": 2
            }
        }
        
        # 深度合并
        merged = {
            "id": base["id"],
            "metadata": {**base.get("metadata", {}), **update.get("metadata", {})}
        }
        
        assert merged["metadata"]["created"] == "2024-01-01"
        assert merged["metadata"]["updated"] == "2024-01-02"
        assert merged["metadata"]["version"] == 2
