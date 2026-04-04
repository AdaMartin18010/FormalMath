#!/bin/bash
# 生成自签名 SSL 证书（仅用于测试环境）

CERT_DIR="/etc/nginx/ssl"
DOMAIN="formalmath.example.com"
DAYS=365

# 创建目录
mkdir -p $CERT_DIR

# 生成私钥
openssl genrsa -out $CERT_DIR/formalmath.key 2048

# 生成证书签名请求
openssl req -new -key $CERT_DIR/formalmath.key \
    -out $CERT_DIR/formalmath.csr \
    -subj "/C=CN/ST=Beijing/L=Beijing/O=FormalMath/OU=IT/CN=$DOMAIN"

# 生成自签名证书
openssl x509 -req -days $DAYS \
    -in $CERT_DIR/formalmath.csr \
    -signkey $CERT_DIR/formalmath.key \
    -out $CERT_DIR/formalmath.crt

# 生成 DH 参数（可选，提高安全性）
openssl dhparam -out $CERT_DIR/dhparam.pem 2048

# 创建证书链文件（自签名证书不需要，但为兼容性保留）
cp $CERT_DIR/formalmath.crt $CERT_DIR/chain.crt

echo "证书生成完成："
echo "  证书: $CERT_DIR/formalmath.crt"
echo "  私钥: $CERT_DIR/formalmath.key"
echo "  DH参数: $CERT_DIR/dhparam.pem"
echo ""
echo "警告：自签名证书仅用于测试，生产环境请使用 Let's Encrypt 或商业证书"
