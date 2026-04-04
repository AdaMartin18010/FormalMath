"""
SSL/TLS配置

提供HTTPS证书配置和SSL上下文设置
"""
import ssl
import logging
from pathlib import Path
from typing import Optional, Tuple, Dict, Any

logger = logging.getLogger(__name__)


class SSLConfig:
    """
    SSL/TLS配置类
    
    支持的配置：
    - 证书和私钥
    - TLS版本（最低TLS 1.2）
    - 密码套件
    - HSTS配置
    """
    
    # 推荐的TLS版本
    MIN_TLS_VERSION = ssl.TLSVersion.TLSv1_2
    
    # 推荐的密码套件（安全性优先）
    RECOMMENDED_CIPHERS = [
        # TLS 1.3
        "TLS_AES_256_GCM_SHA384",
        "TLS_CHACHA20_POLY1305_SHA256",
        "TLS_AES_128_GCM_SHA256",
        # TLS 1.2
        "ECDHE-ECDSA-AES256-GCM-SHA384",
        "ECDHE-RSA-AES256-GCM-SHA384",
        "ECDHE-ECDSA-CHACHA20-POLY1305",
        "ECDHE-RSA-CHACHA20-POLY1305",
        "ECDHE-ECDSA-AES128-GCM-SHA256",
        "ECDHE-RSA-AES128-GCM-SHA256",
    ]
    
    def __init__(
        self,
        cert_file: Optional[str] = None,
        key_file: Optional[str] = None,
        ca_file: Optional[str] = None,
        min_tls_version: ssl.TLSVersion = None,
        ciphers: Optional[str] = None,
        verify_mode: ssl.VerifyMode = ssl.CERT_NONE
    ):
        self.cert_file = cert_file
        self.key_file = key_file
        self.ca_file = ca_file
        self.min_tls_version = min_tls_version or self.MIN_TLS_VERSION
        self.ciphers = ciphers or ":".join(self.RECOMMENDED_CIPHERS)
        self.verify_mode = verify_mode
    
    def create_ssl_context(self) -> Optional[ssl.SSLContext]:
        """
        创建SSL上下文
        
        Returns:
            SSL上下文对象，如果未配置证书则返回None
        """
        if not self.cert_file or not self.key_file:
            logger.warning("未配置SSL证书，将使用HTTP")
            return None
        
        # 检查证书文件是否存在
        cert_path = Path(self.cert_file)
        key_path = Path(self.key_file)
        
        if not cert_path.exists():
            raise FileNotFoundError(f"证书文件不存在: {self.cert_file}")
        if not key_path.exists():
            raise FileNotFoundError(f"私钥文件不存在: {self.key_file}")
        
        # 创建SSL上下文
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        
        # 设置最低TLS版本
        context.minimum_version = self.min_tls_version
        
        # 禁用不安全的TLS版本
        context.options |= ssl.OP_NO_TLSv1
        context.options |= ssl.OP_NO_TLSv1_1
        context.options |= ssl.OP_NO_SSLv2
        context.options |= ssl.OP_NO_SSLv3
        
        # 设置密码套件
        context.set_ciphers(self.ciphers)
        
        # 加载证书
        context.load_cert_chain(
            certfile=self.cert_file,
            keyfile=self.key_file
        )
        
        # 加载CA证书（如果配置）
        if self.ca_file and Path(self.ca_file).exists():
            context.load_verify_locations(self.ca_file)
            self.verify_mode = ssl.CERT_OPTIONAL
        
        # 设置验证模式
        context.verify_mode = self.verify_mode
        
        # 启用会话票据（性能优化）
        context.options |= ssl.OP_NO_TICKET
        
        logger.info("SSL上下文创建成功")
        logger.info(f"  - 最低TLS版本: {self.min_tls_version.name}")
        logger.info(f"  - 证书: {self.cert_file}")
        
        return context
    
    @classmethod
    def from_environment(cls) -> "SSLConfig":
        """
        从环境变量创建SSL配置
        
        环境变量：
        - SSL_CERT_FILE: 证书文件路径
        - SSL_KEY_FILE: 私钥文件路径
        - SSL_CA_FILE: CA证书文件路径
        """
        import os
        
        return cls(
            cert_file=os.getenv("SSL_CERT_FILE"),
            key_file=os.getenv("SSL_KEY_FILE"),
            ca_file=os.getenv("SSL_CA_FILE"),
            min_tls_version=cls.MIN_TLS_VERSION,
        )


class HSTSConfig:
    """
    HSTS (HTTP Strict Transport Security) 配置
    
    强制浏览器使用HTTPS访问网站
    """
    
    def __init__(
        self,
        max_age: int = 31536000,  # 1年
        include_subdomains: bool = True,
        preload: bool = True,
        exempt_paths: Optional[list] = None
    ):
        self.max_age = max_age
        self.include_subdomains = include_subdomains
        self.preload = preload
        self.exempt_paths = exempt_paths or []
    
    def get_header_value(self) -> str:
        """获取HSTS响应头值"""
        value = f"max-age={self.max_age}"
        if self.include_subdomains:
            value += "; includeSubDomains"
        if self.preload:
            value += "; preload"
        return value
    
    def is_exempt(self, path: str) -> bool:
        """检查路径是否豁免HSTS"""
        return any(path.startswith(exempt) for exempt in self.exempt_paths)


def create_ssl_context_for_uvicorn(
    cert_file: str,
    key_file: str,
    ca_file: Optional[str] = None
) -> ssl.SSLContext:
    """
    为Uvicorn创建SSL上下文
    
    Args:
        cert_file: 证书文件路径
        key_file: 私钥文件路径
        ca_file: CA证书文件路径（可选）
    
    Returns:
        SSLContext对象
    """
    config = SSLConfig(
        cert_file=cert_file,
        key_file=key_file,
        ca_file=ca_file
    )
    return config.create_ssl_context()


def get_ssl_uvicorn_config(ssl_config: SSLConfig) -> Dict[str, Any]:
    """
    获取Uvicorn的SSL配置
    
    Args:
        ssl_config: SSL配置对象
    
    Returns:
        Uvicorn配置字典
    """
    context = ssl_config.create_ssl_context()
    if not context:
        return {}
    
    return {
        "ssl_keyfile": ssl_config.key_file,
        "ssl_certfile": ssl_config.cert_file,
        "ssl_version": ssl.PROTOCOL_TLS_SERVER,
        "ssl_cert_reqs": ssl_config.verify_mode,
        "ssl_ca_certs": ssl_config.ca_file,
        "ssl_ciphers": ssl_config.ciphers,
    }
