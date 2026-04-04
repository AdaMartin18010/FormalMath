"""
性能分析工具
Performance Profiling Tools

提供系统性能监控、内存分析和代码剖析功能
"""

import time
import functools
import tracemalloc
import cProfile
import pstats
import io
from typing import Callable, Any, Dict, List, Optional
from contextlib import contextmanager
from dataclasses import dataclass
from memory_profiler import profile as mem_profile
import psutil


@dataclass
class PerformanceMetrics:
    """性能指标数据类"""
    execution_time: float
    memory_usage: float
    cpu_percent: float
    peak_memory: float
    call_count: int = 1
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "execution_time_ms": round(self.execution_time * 1000, 2),
            "memory_usage_mb": round(self.memory_usage / 1024 / 1024, 2),
            "peak_memory_mb": round(self.peak_memory / 1024 / 1024, 2),
            "cpu_percent": round(self.cpu_percent, 2),
            "call_count": self.call_count
        }


class PerformanceProfiler:
    """性能分析器"""
    
    def __init__(self):
        self.metrics_history: List[Dict[str, Any]] = []
    
    @contextmanager
    def profile_block(self, name: str = "code_block"):
        """性能分析上下文管理器"""
        # 开始内存跟踪
        tracemalloc.start()
        start_mem = tracemalloc.get_traced_memory()
        
        # 获取初始CPU
        process = psutil.Process()
        start_cpu = process.cpu_percent()
        
        # 计时开始
        start_time = time.perf_counter()
        
        try:
            yield
        finally:
            # 计时结束
            execution_time = time.perf_counter() - start_time
            
            # 内存统计
            end_mem = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            
            # CPU统计
            cpu_percent = process.cpu_percent()
            
            metrics = PerformanceMetrics(
                execution_time=execution_time,
                memory_usage=end_mem[0] - start_mem[0],
                peak_memory=end_mem[1],
                cpu_percent=cpu_percent
            )
            
            self.metrics_history.append({
                "name": name,
                **metrics.to_dict()
            })
            
            # 打印结果
            print(f"\n📊 性能分析 [{name}]:")
            print(f"  执行时间: {metrics.execution_time * 1000:.2f} ms")
            print(f"  内存使用: {metrics.memory_usage / 1024 / 1024:.2f} MB")
            print(f"  峰值内存: {metrics.peak_memory / 1024 / 1024:.2f} MB")
            print(f"  CPU使用: {metrics.cpu_percent:.2f}%")
    
    def profile_function(self, func: Callable) -> Callable:
        """函数性能分析装饰器"""
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            with self.profile_block(func.__name__):
                return func(*args, **kwargs)
        return wrapper
    
    def get_summary(self) -> Dict[str, Any]:
        """获取性能汇总"""
        if not self.metrics_history:
            return {}
        
        total_time = sum(m["execution_time_ms"] for m in self.metrics_history)
        total_memory = sum(m["memory_usage_mb"] for m in self.metrics_history)
        
        return {
            "total_blocks": len(self.metrics_history),
            "total_time_ms": round(total_time, 2),
            "total_memory_mb": round(total_memory, 2),
            "avg_time_per_block_ms": round(total_time / len(self.metrics_history), 2),
            "blocks": self.metrics_history
        }


class MemoryProfiler:
    """内存分析器"""
    
    @staticmethod
    def get_memory_info() -> Dict[str, Any]:
        """获取当前内存信息"""
        process = psutil.Process()
        memory = process.memory_info()
        
        return {
            "rss_mb": round(memory.rss / 1024 / 1024, 2),
            "vms_mb": round(memory.vms / 1024 / 1024, 2),
            "percent": psutil.virtual_memory().percent,
            "available_mb": round(psutil.virtual_memory().available / 1024 / 1024, 2)
        }
    
    @staticmethod
    @contextmanager
    def track_memory(threshold_mb: float = 100):
        """跟踪内存使用，超过阈值时警告"""
        tracemalloc.start()
        start_mem = tracemalloc.get_traced_memory()
        
        try:
            yield
        finally:
            end_mem = tracemalloc.get_traced_memory()
            tracemalloc.stop()
            
            used_mb = (end_mem[1] - start_mem[0]) / 1024 / 1024
            
            if used_mb > threshold_mb:
                print(f"⚠️  内存使用警告: 使用了 {used_mb:.2f} MB (阈值: {threshold_mb} MB)")
            else:
                print(f"✅ 内存使用正常: {used_mb:.2f} MB")
    
    @staticmethod
    def find_memory_leaks(iterations: int = 10) -> List[Dict[str, Any]]:
        """查找内存泄漏嫌疑"""
        tracemalloc.start()
        
        # 记录初始状态
        snapshots = [tracemalloc.take_snapshot()]
        
        for i in range(iterations):
            time.sleep(0.1)
            snapshots.append(tracemalloc.take_snapshot())
        
        tracemalloc.stop()
        
        # 比较快照
        leaks = []
        for i in range(1, len(snapshots)):
            stats = snapshots[i].compare_to(snapshots[i-1], 'lineno')
            for stat in stats[:3]:  # 前3个增长最多的
                if stat.size_diff > 1024 * 1024:  # 超过1MB
                    leaks.append({
                        "file": stat.traceback.format()[-1],
                        "size_diff_mb": round(stat.size_diff / 1024 / 1024, 2),
                        "count_diff": stat.count_diff
                    })
        
        return leaks


class CodeProfiler:
    """代码性能剖析器"""
    
    @staticmethod
    def profile_with_cprofile(func: Callable, *args, **kwargs) -> Dict[str, Any]:
        """使用cProfile进行代码剖析"""
        profiler = cProfile.Profile()
        profiler.enable()
        
        result = func(*args, **kwargs)
        
        profiler.disable()
        
        # 获取统计信息
        s = io.StringIO()
        ps = pstats.Stats(profiler, stream=s).sort_stats('cumulative')
        ps.print_stats(20)  # 打印前20个
        
        return {
            "result": result,
            "profile_stats": s.getvalue()
        }
    
    @staticmethod
    def get_hotspots(func: Callable, *args, **kwargs) -> List[Dict[str, Any]]:
        """获取性能热点"""
        profiler = cProfile.Profile()
        profiler.enable()
        
        func(*args, **kwargs)
        
        profiler.disable()
        
        stats = pstats.Stats(profiler)
        hotspots = []
        
        for func_name, (cc, nc, tt, ct, callers) in stats.stats.items():
            if ct > 0.1:  # 累计时间超过0.1秒
                hotspots.append({
                    "function": f"{func_name[0]}:{func_name[1]}({func_name[2]})",
                    "call_count": cc,
                    "total_time": round(tt, 4),
                    "cumulative_time": round(ct, 4)
                })
        
        # 按累计时间排序
        hotspots.sort(key=lambda x: x["cumulative_time"], reverse=True)
        return hotspots[:10]  # 返回前10个热点


# 便捷装饰器
def performance_monitor(func: Callable) -> Callable:
    """性能监控装饰器"""
    @functools.wraps(func)
    def wrapper(*args, **kwargs):
        profiler = PerformanceProfiler()
        with profiler.profile_block(func.__name__):
            return func(*args, **kwargs)
    return wrapper


def memory_monitor(threshold_mb: float = 100):
    """内存监控装饰器"""
    def decorator(func: Callable) -> Callable:
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            with MemoryProfiler.track_memory(threshold_mb):
                return func(*args, **kwargs)
        return wrapper
    return decorator


# 系统监控
class SystemMonitor:
    """系统资源监控"""
    
    @staticmethod
    def get_system_info() -> Dict[str, Any]:
        """获取系统信息"""
        return {
            "cpu": {
                "percent": psutil.cpu_percent(interval=1),
                "count": psutil.cpu_count(),
                "freq_mhz": psutil.cpu_freq().current if psutil.cpu_freq() else None
            },
            "memory": {
                "total_gb": round(psutil.virtual_memory().total / 1024 / 1024 / 1024, 2),
                "available_gb": round(psutil.virtual_memory().available / 1024 / 1024 / 1024, 2),
                "percent": psutil.virtual_memory().percent
            },
            "disk": {
                "total_gb": round(psutil.disk_usage('/').total / 1024 / 1024 / 1024, 2),
                "free_gb": round(psutil.disk_usage('/').free / 1024 / 1024 / 1024, 2),
                "percent": psutil.disk_usage('/').percent
            },
            "network": {
                "bytes_sent_mb": round(psutil.net_io_counters().bytes_sent / 1024 / 1024, 2),
                "bytes_recv_mb": round(psutil.net_io_counters().bytes_recv / 1024 / 1024, 2)
            }
        }
    
    @staticmethod
    def monitor_process(pid: Optional[int] = None, duration: int = 10) -> List[Dict[str, Any]]:
        """监控进程资源使用"""
        if pid is None:
            pid = psutil.Process().pid
        
        process = psutil.Process(pid)
        samples = []
        
        for _ in range(duration):
            samples.append({
                "timestamp": time.time(),
                "cpu_percent": process.cpu_percent(),
                "memory_mb": round(process.memory_info().rss / 1024 / 1024, 2),
                "connections": len(process.connections()),
                "threads": process.num_threads()
            })
            time.sleep(1)
        
        return samples


# 使用示例
if __name__ == "__main__":
    print("=" * 60)
    print("性能分析工具示例")
    print("=" * 60)
    
    # 1. 系统信息
    print("\n1. 系统信息:")
    info = SystemMonitor.get_system_info()
    print(f"  CPU: {info['cpu']['percent']}% ({info['cpu']['count']}核)")
    print(f"  内存: {info['memory']['percent']}% 使用")
    print(f"  磁盘: {info['disk']['percent']}% 使用")
    
    # 2. 性能分析示例
    print("\n2. 代码性能分析:")
    profiler = PerformanceProfiler()
    
    @profiler.profile_function
    def test_function():
        """测试函数"""
        data = []
        for i in range(10000):
            data.append(i ** 2)
        return sum(data)
    
    result = test_function()
    print(f"  结果: {result}")
    
    # 3. 内存分析
    print("\n3. 内存分析:")
    mem_info = MemoryProfiler.get_memory_info()
    print(f"  RSS: {mem_info['rss_mb']} MB")
    print(f"  系统内存使用率: {mem_info['percent']}%")
    
    # 4. 性能热点分析
    print("\n4. 性能热点分析:")
    
    def cpu_intensive():
        """CPU密集型函数"""
        result = 0
        for i in range(1000000):
            result += i ** 0.5
        return result
    
    hotspots = CodeProfiler.get_hotspots(cpu_intensive)
    for i, hotspot in enumerate(hotspots[:3], 1):
        print(f"  {i}. {hotspot['function']}")
        print(f"     累计时间: {hotspot['cumulative_time']}s")
    
    print("\n" + "=" * 60)
    print("分析完成!")
