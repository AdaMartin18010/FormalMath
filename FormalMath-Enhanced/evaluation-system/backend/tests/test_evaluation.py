"""Tests for evaluation system."""
import pytest
from fastapi.testclient import TestClient
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker
from sqlalchemy.pool import StaticPool

from main import app
from app.core.database import Base, get_db


# Setup test database
SQLALCHEMY_DATABASE_URL = "sqlite:///:memory:"
engine = create_engine(
    SQLALCHEMY_DATABASE_URL,
    connect_args={"check_same_thread": False},
    poolclass=StaticPool,
)
TestingSessionLocal = sessionmaker(autocommit=False, autoflush=False, bind=engine)


def override_get_db():
    """Override database dependency for testing."""
    try:
        db = TestingSessionLocal()
        yield db
    finally:
        db.close()


app.dependency_overrides[get_db] = override_get_db

client = TestClient(app)


@pytest.fixture(scope="function")
def setup_db():
    """Setup test database."""
    Base.metadata.create_all(bind=engine)
    yield
    Base.metadata.drop_all(bind=engine)


class TestEvaluationAPI:
    """Test evaluation API endpoints."""
    
    def test_root(self, setup_db):
        """Test root endpoint."""
        response = client.get("/")
        assert response.status_code == 200
        assert "name" in response.json()
    
    def test_health_check(self, setup_db):
        """Test health check endpoint."""
        response = client.get("/health")
        assert response.status_code == 200
        assert response.json()["status"] == "healthy"
    
    def test_assess_endpoint(self, setup_db):
        """Test assessment endpoint."""
        payload = {
            "user_id": "user123",
            "scores": {
                "knowledge_mastery": 85.0,
                "problem_solving": 78.0,
                "proof_ability": 72.0,
                "application": 80.0,
                "innovation": 65.0
            },
            "evaluation_type": "comprehensive",
            "period": "2024-Q1"
        }
        
        response = client.post("/api/evaluation/assess", json=payload)
        assert response.status_code == 200
        
        data = response.json()
        assert data["user_id"] == "user123"
        assert "record_id" in data
        assert "scores" in data
        assert "weighted_score" in data["scores"]
    
    def test_get_dimensions(self, setup_db):
        """Test get dimensions endpoint."""
        response = client.get("/api/evaluation/dimensions")
        assert response.status_code == 200
        
        data = response.json()
        assert "dimensions" in data
        assert len(data["dimensions"]) == 5
    
    def test_create_and_get_report(self, setup_db):
        """Test create assessment and get report."""
        # Create assessment
        payload = {
            "user_id": "user456",
            "scores": {
                "knowledge_mastery": 90.0,
                "problem_solving": 85.0,
                "proof_ability": 88.0,
                "application": 82.0,
                "innovation": 75.0
            }
        }
        
        response = client.post("/api/evaluation/assess", json=payload)
        assert response.status_code == 200
        
        # Get report
        response = client.get("/api/evaluation/report/user456")
        assert response.status_code == 200
        
        data = response.json()
        assert "report_metadata" in data
        assert "executive_summary" in data
        assert "detailed_scores" in data
    
    def test_generate_feedback(self, setup_db):
        """Test feedback generation."""
        # Create assessment first
        payload = {
            "user_id": "user789",
            "scores": {
                "knowledge_mastery": 70.0,
                "problem_solving": 65.0,
                "proof_ability": 60.0,
                "application": 68.0,
                "innovation": 55.0
            }
        }
        
        response = client.post("/api/evaluation/assess", json=payload)
        assert response.status_code == 200
        record_id = response.json()["record_id"]
        
        # Generate feedback
        feedback_payload = {
            "user_id": "user789",
            "record_id": record_id
        }
        
        response = client.post("/api/evaluation/feedback", json=feedback_payload)
        assert response.status_code == 200
        
        data = response.json()
        assert "feedback_id" in data
        assert "summary" in data
        assert "suggestions" in data
    
    def test_get_progress(self, setup_db):
        """Test get learning progress."""
        # Create multiple assessments
        for i in range(3):
            payload = {
                "user_id": "user_progress",
                "scores": {
                    "knowledge_mastery": 70.0 + i * 5,
                    "problem_solving": 65.0 + i * 5,
                    "proof_ability": 60.0 + i * 5,
                    "application": 68.0 + i * 5,
                    "innovation": 55.0 + i * 5
                },
                "period": f"2024-Q{i+1}"
            }
            response = client.post("/api/evaluation/assess", json=payload)
            assert response.status_code == 200
        
        # Get progress
        response = client.get("/api/evaluation/progress/user_progress")
        assert response.status_code == 200
        
        data = response.json()
        assert data["user_id"] == "user_progress"
        assert "trajectory" in data
        assert len(data["trajectory"]) >= 3


class TestEvaluationModel:
    """Test evaluation model."""
    
    def test_model_calculation(self):
        """Test model score calculation."""
        from app.evaluation.model import EvaluationModel
        
        model = EvaluationModel()
        assessments = {
            'knowledge_mastery': 80.0,
            'problem_solving': 75.0,
            'proof_ability': 70.0,
            'application': 85.0,
            'innovation': 60.0
        }
        
        result = model.calculate_score(assessments)
        
        assert 'total_score' in result
        assert 'weighted_score' in result
        assert 'grade' in result
        assert 'dimension_scores' in result
        
        # Check weighted calculation
        expected_weighted = (
            80.0 * 0.30 + 75.0 * 0.25 + 70.0 * 0.20 + 
            85.0 * 0.15 + 60.0 * 0.10
        )
        assert abs(result['weighted_score'] - expected_weighted) < 0.01
    
    def test_grade_calculation(self):
        """Test grade calculation."""
        from app.evaluation.model import EvaluationModel
        
        model = EvaluationModel()
        
        assert model._calculate_grade(95) == 'A'
        assert model._calculate_grade(85) == 'B'
        assert model._calculate_grade(75) == 'C'
        assert model._calculate_grade(65) == 'D'
        assert model._calculate_grade(55) == 'F'
    
    def test_growth_calculation(self):
        """Test growth calculation."""
        from app.evaluation.model import EvaluationModel
        
        model = EvaluationModel()
        current = {
            'knowledge_mastery': 80.0,
            'problem_solving': 75.0
        }
        previous = {
            'knowledge_mastery': 70.0,
            'problem_solving': 70.0
        }
        
        growth = model.calculate_growth(current, previous)
        
        assert 'dimension_growth' in growth
        assert growth['dimension_growth']['knowledge_mastery']['absolute_growth'] == 10.0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
