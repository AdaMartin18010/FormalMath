/**
 * PWA 图标生成脚本
 * 需要安装 sharp: npm install -D sharp
 * 
 * 使用说明:
 * node scripts/generate-icons.js
 */

const fs = require('fs');
const path = require('path');

// 检查 sharp 是否安装
try {
  const sharp = require('sharp');
  
  const sizes = [72, 96, 128, 144, 152, 192, 384, 512];
  const inputFile = path.join(__dirname, '../public/icons/icon.svg');
  const outputDir = path.join(__dirname, '../public/icons');
  
  // 确保输出目录存在
  if (!fs.existsSync(outputDir)) {
    fs.mkdirSync(outputDir, { recursive: true });
  }
  
  async function generateIcons() {
    console.log('正在生成 PWA 图标...');
    
    for (const size of sizes) {
      const outputFile = path.join(outputDir, `icon-${size}x${size}.png`);
      
      try {
        await sharp(inputFile)
          .resize(size, size)
          .png()
          .toFile(outputFile);
        
        console.log(`✓ 生成: icon-${size}x${size}.png`);
      } catch (error) {
        console.error(`✗ 失败: icon-${size}x${size}.png`, error.message);
      }
    }
    
    // 生成特殊用途图标
    const specialIcons = [
      { name: 'graph', size: 96 },
      { name: 'tree', size: 96 },
      { name: 'mindmap', size: 96 },
    ];
    
    for (const { name, size } of specialIcons) {
      const outputFile = path.join(outputDir, `${name}-${size}x${size}.png`);
      
      try {
        await sharp(inputFile)
          .resize(size, size)
          .png()
          .toFile(outputFile);
        
        console.log(`✓ 生成: ${name}-${size}x${size}.png`);
      } catch (error) {
        console.error(`✗ 失败: ${name}-${size}x${size}.png`, error.message);
      }
    }
    
    console.log('\n图标生成完成!');
  }
  
  generateIcons().catch(console.error);
  
} catch (error) {
  console.log('请安装 sharp 以生成图标:');
  console.log('npm install -D sharp');
  console.log('\n或者手动转换 SVG 图标为 PNG 格式。');
}
