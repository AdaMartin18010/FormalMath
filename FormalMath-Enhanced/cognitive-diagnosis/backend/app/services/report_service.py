"""
报告服务
"""

from typing import List, Optional, Dict, Any

from app.models.diagnosis import DiagnosisReport
from app.database.in_memory_db import InMemoryDatabase


class ReportService:
    """报告服务"""
    
    def __init__(self):
        self.db = InMemoryDatabase()
    
    def get_user_reports(
        self,
        user_id: str,
        limit: int = 10,
        offset: int = 0
    ) -> List[DiagnosisReport]:
        """获取用户的诊断报告"""
        return self.db.get_user_reports(user_id, limit=limit, offset=offset)
    
    def count_user_reports(self, user_id: str) -> int:
        """统计用户的报告数量"""
        return self.db.count_user_reports(user_id)
    
    def get_report_by_id(self, report_id: str) -> Optional[DiagnosisReport]:
        """根据ID获取报告"""
        return self.db.get_report(report_id)
    
    def get_report_summary(self, report_id: str) -> Optional[Dict[str, Any]]:
        """获取报告摘要"""
        report = self.db.get_report(report_id)
        if not report:
            return None
        
        return {
            "report_id": report.id,
            "diagnosis_id": report.diagnosis_id,
            "user_id": report.user_id,
            "created_at": report.created_at.isoformat(),
            "ability_level": report.ability_level,
            "accuracy": report.accuracy,
            "suggestion_count": len(report.suggestions),
            "key_suggestions": [
                {
                    "type": s.type,
                    "title": s.title,
                    "priority": s.priority
                }
                for s in report.suggestions[:3]
            ]
        }
    
    def compare_reports(
        self,
        report_id: str,
        compare_with: Optional[str] = None
    ) -> Dict[str, Any]:
        """对比报告"""
        report1 = self.db.get_report(report_id)
        if not report1:
            raise ValueError("报告不存在")
        
        # 如果没有指定对比报告，使用用户的上一次报告
        if not compare_with:
            user_reports = self.db.get_user_reports(report1.user_id, limit=5)
            for r in user_reports:
                if r.id != report_id:
                    compare_with = r.id
                    break
        
        if not compare_with:
            return {
                "has_comparison": False,
                "message": "没有可对比的历史报告"
            }
        
        report2 = self.db.get_report(compare_with)
        if not report2:
            return {
                "has_comparison": False,
                "message": "对比报告不存在"
            }
        
        # 计算能力水平变化
        ability_changes = {}
        for level in range(4):
            old_val = report2.ability_level.get(level, 0.0)
            new_val = report1.ability_level.get(level, 0.0)
            ability_changes[f"L{level}"] = {
                "old": round(old_val * 100, 1),
                "new": round(new_val * 100, 1),
                "change": round((new_val - old_val) * 100, 1)
            }
        
        # 计算正确率变化
        accuracy_change = report1.accuracy - report2.accuracy
        
        return {
            "has_comparison": True,
            "current_report_id": report_id,
            "compared_with_id": compare_with,
            "ability_changes": ability_changes,
            "accuracy_change": {
                "old": round(report2.accuracy * 100, 1),
                "new": round(report1.accuracy * 100, 1),
                "change": round(accuracy_change * 100, 1)
            },
            "summary": self._generate_comparison_summary(ability_changes, accuracy_change)
        }
    
    def _generate_comparison_summary(
        self,
        ability_changes: Dict[str, Dict],
        accuracy_change: float
    ) -> str:
        """生成对比总结"""
        improvements = []
        declines = []
        
        for level, change in ability_changes.items():
            if change["change"] > 5:
                improvements.append(f"{level}(+{change['change']}%)")
            elif change["change"] < -5:
                declines.append(f"{level}({change['change']}%)")
        
        parts = []
        
        if improvements:
            parts.append(f"在{', '.join(improvements)}有显著提升")
        
        if declines:
            parts.append(f"在{', '.join(declines)}有所下降")
        
        if accuracy_change > 0.1:
            parts.append("整体正确率提高")
        elif accuracy_change < -0.1:
            parts.append("整体正确率下降")
        
        if not parts:
            return "能力水平保持稳定"
        
        return "；".join(parts)
    
    def export_report(self, report_id: str, format: str = "json") -> Any:
        """导出报告"""
        report = self.db.get_report(report_id)
        if not report:
            raise ValueError("报告不存在")
        
        if format == "json":
            return report.model_dump()
        elif format == "html":
            return self._export_to_html(report)
        elif format == "pdf":
            return {"message": "PDF导出功能需要安装reportlab库"}
        else:
            raise ValueError(f"不支持的格式: {format}")
    
    def _export_to_html(self, report: DiagnosisReport) -> str:
        """导出为HTML"""
        html = f"""
        <!DOCTYPE html>
        <html>
        <head>
            <title>诊断报告 - {report.id}</title>
            <style>
                body {{ font-family: Arial, sans-serif; max-width: 800px; margin: 0 auto; padding: 20px; }}
                h1 {{ color: #333; }}
                .section {{ margin: 20px 0; padding: 15px; background: #f5f5f5; border-radius: 5px; }}
                .ability-level {{ display: flex; justify-content: space-between; margin: 10px 0; }}
                .suggestion {{ margin: 10px 0; padding: 10px; background: white; border-left: 4px solid #2196F3; }}
            </style>
        </head>
        <body>
            <h1>认知诊断报告</h1>
            <p>报告ID: {report.id}</p>
            <p>生成时间: {report.created_at.strftime('%Y-%m-%d %H:%M')}</p>
            
            <div class="section">
                <h2>能力水平评估</h2>
                <div class="ability-level"><span>L0-基础层</span><span>{report.ability_level.get(0, 0)*100:.1f}%</span></div>
                <div class="ability-level"><span>L1-中级层</span><span>{report.ability_level.get(1, 0)*100:.1f}%</span></div>
                <div class="ability-level"><span>L2-高级层</span><span>{report.ability_level.get(2, 0)*100:.1f}%</span></div>
                <div class="ability-level"><span>L3-研究层</span><span>{report.ability_level.get(3, 0)*100:.1f}%</span></div>
            </div>
            
            <div class="section">
                <h2>学习建议</h2>
        """
        
        for suggestion in report.suggestions[:5]:
            html += f"""
                <div class="suggestion">
                    <strong>{suggestion.title}</strong>
                    <p>{suggestion.content}</p>
                </div>
            """
        
        html += """
            </div>
        </body>
        </html>
        """
        
        return html
