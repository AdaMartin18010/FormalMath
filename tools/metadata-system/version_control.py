#!/usr/bin/env python3
"""
FormalMath 版本控制系统
管理文档版本历史、变更追踪和回滚
"""

import os
import json
import hashlib
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass, asdict
import shutil


@dataclass
class VersionInfo:
    """版本信息"""
    version: str
    date: str
    author: str
    changes: str
    commit_hash: Optional[str] = None
    
    def to_dict(self) -> Dict:
        return asdict(self)


@dataclass
class ChangeRecord:
    """变更记录"""
    filepath: str
    old_version: str
    new_version: str
    change_type: str  # created, modified, deleted
    timestamp: str
    diff_summary: str
    author: str
    checksum_before: Optional[str] = None
    checksum_after: Optional[str] = None


class VersionControl:
    """文档版本控制系统"""
    
    def __init__(self, root_dir: str = '.', history_dir: str = '.metadata_history'):
        self.root_dir = Path(root_dir)
        self.history_dir = self.root_dir / history_dir
        self.history_dir.mkdir(exist_ok=True)
        
        self.changelog_path = self.history_dir / 'changelog.json'
        self.changelog = self._load_changelog()
    
    def _load_changelog(self) -> Dict:
        """加载变更日志"""
        if self.changelog_path.exists():
            with open(self.changelog_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        return {'versions': [], 'changes': []}
    
    def _save_changelog(self):
        """保存变更日志"""
        with open(self.changelog_path, 'w', encoding='utf-8') as f:
            json.dump(self.changelog, f, ensure_ascii=False, indent=2)
    
    def _calculate_checksum(self, filepath: Path) -> str:
        """计算文件校验和"""
        if not filepath.exists():
            return ''
        content = filepath.read_bytes()
        return hashlib.md5(content).hexdigest()
    
    def _parse_version(self, version: str) -> Tuple[int, int, int]:
        """解析版本号"""
        parts = version.split('.')
        return (int(parts[0]), int(parts[1]), int(parts[2]))
    
    def increment_version(self, version: str, level: str = 'patch') -> str:
        """
        增加版本号
        
        Args:
            version: 当前版本号
            level: 增加级别 (major, minor, patch)
        """
        major, minor, patch = self._parse_version(version)
        
        if level == 'major':
            return f"{major + 1}.0.0"
        elif level == 'minor':
            return f"{major}.{minor + 1}.0"
        else:  # patch
            return f"{major}.{minor}.{patch + 1}"
    
    def backup_file(self, filepath: Path, version: str) -> Path:
        """
        备份文件
        
        Args:
            filepath: 文件路径
            version: 版本号
        
        Returns:
            备份文件路径
        """
        rel_path = filepath.relative_to(self.root_dir)
        backup_name = f"{rel_path.parent.as_posix().replace('/', '_')}_{filepath.stem}_{version}{filepath.suffix}"
        backup_path = self.history_dir / backup_name
        
        shutil.copy2(filepath, backup_path)
        return backup_path
    
    def record_change(self, 
                      filepath: str,
                      old_version: str,
                      new_version: str,
                      change_type: str,
                      changes: str,
                      author: str = 'System'):
        """
        记录变更
        
        Args:
            filepath: 文件路径
            old_version: 旧版本
            new_version: 新版本
            change_type: 变更类型
            changes: 变更描述
            author: 作者
        """
        full_path = self.root_dir / filepath
        
        record = ChangeRecord(
            filepath=filepath,
            old_version=old_version,
            new_version=new_version,
            change_type=change_type,
            timestamp=datetime.now().isoformat(),
            diff_summary=changes,
            author=author
        )
        
        # 添加版本信息
        version_info = VersionInfo(
            version=new_version,
            date=datetime.now().strftime('%Y-%m-%d'),
            author=author,
            changes=changes
        )
        
        # 更新变更日志
        self.changelog['changes'].append(asdict(record))
        self.changelog['versions'].append(version_info.to_dict())
        
        self._save_changelog()
        
        print(f"已记录变更: {filepath} {old_version} -> {new_version}")
    
    def get_file_history(self, filepath: str) -> List[Dict]:
        """
        获取文件历史
        
        Args:
            filepath: 文件路径
        
        Returns:
            历史记录列表
        """
        history = []
        for change in self.changelog['changes']:
            if change['filepath'] == filepath:
                history.append(change)
        return history
    
    def compare_versions(self, filepath: str, version1: str, version2: str) -> str:
        """
        比较两个版本
        
        Args:
            filepath: 文件路径
            version1: 版本1
            version2: 版本2
        
        Returns:
            差异摘要
        """
        # 查找备份文件
        pattern1 = f"*{Path(filepath).stem}_{version1}{Path(filepath).suffix}"
        pattern2 = f"*{Path(filepath).stem}_{version2}{Path(filepath).suffix}"
        
        backups1 = list(self.history_dir.glob(pattern1))
        backups2 = list(self.history_dir.glob(pattern2))
        
        if not backups1 or not backups2:
            return "无法找到指定版本的备份"
        
        content1 = backups1[0].read_text(encoding='utf-8')
        content2 = backups2[0].read_text(encoding='utf-8')
        
        # 简单差异比较
        lines1 = content1.split('\n')
        lines2 = content2.split('\n')
        
        added = len([l for l in lines2 if l not in lines1])
        removed = len([l for l in lines1 if l not in lines2])
        
        return f"添加: {added} 行, 删除: {removed} 行"
    
    def rollback(self, filepath: str, target_version: str) -> bool:
        """
        回滚到指定版本
        
        Args:
            filepath: 文件路径
            target_version: 目标版本
        
        Returns:
            是否成功
        """
        # 查找备份
        pattern = f"*{Path(filepath).stem}_{target_version}{Path(filepath).suffix}"
        backups = list(self.history_dir.glob(pattern))
        
        if not backups:
            print(f"错误: 找不到版本 {target_version} 的备份")
            return False
        
        # 备份当前版本
        current_path = self.root_dir / filepath
        if current_path.exists():
            # 读取当前版本
            with open(current_path, 'r', encoding='utf-8') as f:
                import re
                content = f.read()
                version_match = re.search(r'version:\s*([\d.]+)', content)
                current_version = version_match.group(1) if version_match else 'unknown'
            
            self.backup_file(current_path, f"{current_version}_pre_rollback")
        
        # 恢复备份
        shutil.copy2(backups[0], current_path)
        
        print(f"已回滚 {filepath} 到版本 {target_version}")
        return True
    
    def generate_version_report(self, output_path: str = None):
        """
        生成版本报告
        
        Args:
            output_path: 输出路径
        """
        report = {
            'generated_at': datetime.now().isoformat(),
            'total_versions': len(self.changelog['versions']),
            'total_changes': len(self.changelog['changes']),
            'changes_by_type': {},
            'recent_changes': self.changelog['changes'][-20:]
        }
        
        # 统计变更类型
        for change in self.changelog['changes']:
            change_type = change['change_type']
            report['changes_by_type'][change_type] = report['changes_by_type'].get(change_type, 0) + 1
        
        if output_path:
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(report, f, ensure_ascii=False, indent=2)
            print(f"版本报告已保存到: {output_path}")
        
        return report
    
    def print_version_history(self, filepath: str = None):
        """打印版本历史"""
        print("\n" + "="*80)
        print("版本历史")
        print("="*80)
        
        if filepath:
            history = self.get_file_history(filepath)
            print(f"文件: {filepath}")
            print(f"历史记录数: {len(history)}")
            print("-"*80)
            
            for i, h in enumerate(history, 1):
                print(f"{i}. {h['old_version']} -> {h['new_version']}")
                print(f"   时间: {h['timestamp']}")
                print(f"   类型: {h['change_type']}")
                print(f"   变更: {h['diff_summary']}")
                print(f"   作者: {h['author']}")
                print()
        else:
            print(f"总版本数: {len(self.changelog['versions'])}")
            print(f"总变更数: {len(self.changelog['changes'])}")
            print("\n最近10次变更:")
            print("-"*80)
            
            for i, change in enumerate(self.changelog['changes'][-10:], 1):
                print(f"{i}. {change['filepath']}")
                print(f"   {change['old_version']} -> {change['new_version']} ({change['change_type']})")
                print(f"   {change['timestamp'][:19]} by {change['author']}")
                print()
        
        print("="*80)


class MetadataVersionManager:
    """元数据版本管理器"""
    
    def __init__(self, root_dir: str = '.'):
        self.root_dir = Path(root_dir)
        self.vc = VersionControl(root_dir)
    
    def update_document_version(self, 
                                 filepath: str,
                                 changes: str,
                                 level: str = 'patch',
                                 author: str = 'System') -> str:
        """
        更新文档版本
        
        Args:
            filepath: 文件路径
            changes: 变更描述
            level: 版本递增级别
            author: 作者
        
        Returns:
            新版本号
        """
        full_path = self.root_dir / filepath
        
        if not full_path.exists():
            raise FileNotFoundError(f"文件不存在: {filepath}")
        
        # 读取当前内容
        content = full_path.read_text(encoding='utf-8')
        
        # 解析当前版本
        import re
        version_match = re.search(r'version:\s*([\d.]+)', content)
        old_version = version_match.group(1) if version_match else '0.0.0'
        
        # 计算新版本
        new_version = self.vc.increment_version(old_version, level)
        
        # 更新元数据中的版本
        if version_match:
            content = re.sub(r'(version:\s*)[\d.]+', f'\\g<1>{new_version}', content)
        else:
            # 在 YAML 头部添加版本
            if content.startswith('---'):
                content = re.sub(r'^(---\s*\n)', f'\\1version: {new_version}\n', content)
            else:
                content = f"---\nversion: {new_version}\n---\n\n{content}"
        
        # 更新时间戳
        now = datetime.now().strftime('%Y-%m-%dT%H:%M:%SZ')
        if 'last_modified:' in content:
            content = re.sub(r'last_modified:\s*[\d\-T:Z]+', f'last_modified: {now}', content)
        else:
            # 在 YAML 头部添加
            content = re.sub(r'(version:\s*[\d.]+\n)', f'\\1last_modified: {now}\n', content)
        
        # 保存更新后的内容
        full_path.write_text(content, encoding='utf-8')
        
        # 备份旧版本
        self.vc.backup_file(full_path, old_version)
        
        # 记录变更
        self.vc.record_change(
            filepath=filepath,
            old_version=old_version,
            new_version=new_version,
            change_type='modified',
            changes=changes,
            author=author
        )
        
        return new_version
    
    def batch_update_versions(self,
                              filepaths: List[str],
                              changes: str,
                              level: str = 'patch',
                              author: str = 'System') -> Dict[str, str]:
        """
        批量更新文档版本
        
        Args:
            filepaths: 文件路径列表
            changes: 变更描述
            level: 版本递增级别
            author: 作者
        
        Returns:
            路径到新版本的映射
        """
        results = {}
        for filepath in filepaths:
            try:
                new_version = self.update_document_version(filepath, changes, level, author)
                results[filepath] = new_version
            except Exception as e:
                results[filepath] = f"Error: {e}"
        
        return results


def main():
    """主函数"""
    import argparse
    
    parser = argparse.ArgumentParser(description='FormalMath 版本控制系统')
    parser.add_argument('-d', '--directory', default='.', help='项目根目录')
    
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # 更新版本命令
    update_parser = subparsers.add_parser('update', help='更新文档版本')
    update_parser.add_argument('filepath', help='文件路径')
    update_parser.add_argument('changes', help='变更描述')
    update_parser.add_argument('--level', default='patch', choices=['major', 'minor', 'patch'],
                               help='版本递增级别')
    update_parser.add_argument('--author', default='System', help='作者')
    
    # 历史命令
    history_parser = subparsers.add_parser('history', help='查看版本历史')
    history_parser.add_argument('--file', help='指定文件路径')
    
    # 回滚命令
    rollback_parser = subparsers.add_parser('rollback', help='回滚到指定版本')
    rollback_parser.add_argument('filepath', help='文件路径')
    rollback_parser.add_argument('version', help='目标版本号')
    
    # 报告命令
    report_parser = subparsers.add_parser('report', help='生成版本报告')
    report_parser.add_argument('-o', '--output', help='输出文件路径')
    
    args = parser.parse_args()
    
    vc = VersionControl(args.directory)
    
    if args.command == 'update':
        manager = MetadataVersionManager(args.directory)
        new_version = manager.update_document_version(
            args.filepath,
            args.changes,
            args.level,
            args.author
        )
        print(f"版本已更新: {new_version}")
    
    elif args.command == 'history':
        vc.print_version_history(args.file)
    
    elif args.command == 'rollback':
        vc.rollback(args.filepath, args.version)
    
    elif args.command == 'report':
        report = vc.generate_version_report(args.output)
        print(f"\n版本报告:")
        print(f"  总版本数: {report['total_versions']}")
        print(f"  总变更数: {report['total_changes']}")
        print(f"  变更类型统计: {report['changes_by_type']}")
    
    else:
        parser.print_help()


if __name__ == '__main__':
    main()
