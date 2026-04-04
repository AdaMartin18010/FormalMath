/**
 * 性能优化检查脚本
 * 自动检测并提供优化建议
 */

const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

// 颜色输出
const colors = {
  reset: '\x1b[0m',
  bright: '\x1b[1m',
  green: '\x1b[32m',
  yellow: '\x1b[33m',
  red: '\x1b[31m',
  blue: '\x1b[34m',
};

function log(message, color = 'reset') {
  console.log(`${colors[color]}${message}${colors.reset}`);
}

// 检查结果收集器
const results = {
  passed: [],
  warnings: [],
  errors: [],
  suggestions: [],
};

function pass(message) {
  results.passed.push(message);
  log(`  ✓ ${message}`, 'green');
}

function warn(message, suggestion) {
  results.warnings.push({ message, suggestion });
  log(`  ⚠ ${message}`, 'yellow');
  if (suggestion) log(`    → ${suggestion}`, 'blue');
}

function error(message, suggestion) {
  results.errors.push({ message, suggestion });
  log(`  ✗ ${message}`, 'red');
  if (suggestion) log(`    → ${suggestion}`, 'blue');
}

// 检查清单
const checks = {
  // 1. 构建配置检查
  buildConfig() {
    log('\n📦 Build Configuration', 'bright');
    
    const viteConfig = fs.readFileSync('vite.config.ts', 'utf8');
    
    if (viteConfig.includes('manualChunks')) {
      pass('代码分割已配置');
    } else {
      error('代码分割未配置', '在 vite.config.ts 中配置 manualChunks');
    }
    
    if (viteConfig.includes('terser')) {
      pass('Terser 压缩已启用');
    } else {
      warn('建议使用 Terser 压缩', '在 build.minify 中设置 "terser"');
    }
    
    if (viteConfig.includes('drop_console')) {
      pass('生产环境已禁用 console');
    } else {
      warn('建议在生产环境移除 console', '在 terserOptions.compress 中设置 drop_console: true');
    }
    
    if (viteConfig.includes('assetsInlineLimit')) {
      pass('资源内联已配置');
    } else {
      warn('建议配置资源内联限制', '设置 build.assetsInlineLimit');
    }
  },

  // 2. 性能工具检查
  performanceTools() {
    log('\n🚀 Performance Tools', 'bright');
    
    const perfDir = path.join('src', 'utils', 'performance');
    if (fs.existsSync(perfDir)) {
      pass('性能工具目录存在');
      
      const files = ['index.ts', 'cache.ts', 'lazyLoad.ts', 'apiOptimizer.ts', 'performanceMonitor.ts'];
      files.forEach(file => {
        if (fs.existsSync(path.join(perfDir, file))) {
          pass(`  ${file} 存在`);
        } else {
          error(`  ${file} 缺失`, `创建 src/utils/performance/${file}`);
        }
      });
    } else {
      error('性能工具目录不存在', '创建 src/utils/performance/ 目录');
    }
  },

  // 3. 服务器端配置检查
  serverConfig() {
    log('\n🖥️  Server Configuration', 'bright');
    
    const middlewareDir = path.join('server', 'middleware');
    if (fs.existsSync(middlewareDir)) {
      pass('服务器中间件目录存在');
      
      if (fs.existsSync(path.join(middlewareDir, 'cache.js'))) {
        pass('缓存中间件存在');
      } else {
        warn('缓存中间件不存在', '创建 server/middleware/cache.js');
      }
      
      if (fs.existsSync(path.join(middlewareDir, 'performance.js'))) {
        pass('性能监控中间件存在');
      } else {
        warn('性能监控中间件不存在', '创建 server/middleware/performance.js');
      }
    } else {
      warn('服务器中间件目录不存在');
    }
    
    const configDir = path.join('server', 'config');
    if (fs.existsSync(configDir)) {
      if (fs.existsSync(path.join(configDir, 'database.js'))) {
        pass('数据库配置存在');
      } else {
        warn('数据库配置不存在', '创建 server/config/database.js');
      }
    }
  },

  // 4. 图片优化检查
  imageOptimization() {
    log('\n🖼️  Image Optimization', 'bright');
    
    const publicDir = path.join('public');
    if (fs.existsSync(publicDir)) {
      const images = [];
      
      function scanDir(dir) {
        const items = fs.readdirSync(dir);
        for (const item of items) {
          const fullPath = path.join(dir, item);
          const stat = fs.statSync(fullPath);
          if (stat.isDirectory()) {
            scanDir(fullPath);
          } else if (/\.(jpg|jpeg|png|gif)$/i.test(item)) {
            images.push(fullPath);
          }
        }
      }
      
      try {
        scanDir(publicDir);
      } catch (e) {
        // ignore
      }
      
      if (images.length === 0) {
        pass('未检测到需要优化的图片');
      } else {
        warn(`发现 ${images.length} 张未优化的图片`, '建议转换为 WebP/AVIF 格式');
      }
    }
  },

  // 5. 依赖检查
  dependencies() {
    log('\n📚 Dependencies', 'bright');
    
    const packageJson = JSON.parse(fs.readFileSync('package.json', 'utf8'));
    
    // 检查性能相关依赖
    const perfDeps = [
      'compression',
      'lighthouse',
      'puppeteer',
      'chrome-launcher',
    ];
    
    const devDeps = packageJson.devDependencies || {};
    
    perfDeps.forEach(dep => {
      if (devDeps[dep]) {
        pass(`${dep} 已安装`);
      } else {
        warn(`${dep} 未安装`, `运行: npm install --save-dev ${dep}`);
      }
    });
  },

  // 6. 脚本检查
  scripts() {
    log('\n📝 NPM Scripts', 'bright');
    
    const packageJson = JSON.parse(fs.readFileSync('package.json', 'utf8'));
    const scripts = packageJson.scripts || {};
    
    const recommendedScripts = [
      'perf:test',
      'perf:lighthouse',
      'bundle:analyze',
    ];
    
    recommendedScripts.forEach(script => {
      if (scripts[script]) {
        pass(`script "${script}" 已配置`);
      } else {
        warn(`script "${script}" 未配置`, `在 package.json 中添加 "${script}"`);
      }
    });
  },

  // 7. 文件大小检查
  async bundleSize() {
    log('\n📊 Bundle Size Check', 'bright');
    
    const distDir = path.join('dist');
    if (!fs.existsSync(distDir)) {
      warn('dist 目录不存在，跳过大小检查', '先运行 npm run build');
      return;
    }
    
    let totalSize = 0;
    let jsSize = 0;
    let cssSize = 0;
    
    function calcSize(dir) {
      const items = fs.readdirSync(dir);
      for (const item of items) {
        const fullPath = path.join(dir, item);
        const stat = fs.statSync(fullPath);
        if (stat.isDirectory()) {
          calcSize(fullPath);
        } else {
          totalSize += stat.size;
          if (item.endsWith('.js')) jsSize += stat.size;
          if (item.endsWith('.css')) cssSize += stat.size;
        }
      }
    }
    
    try {
      calcSize(distDir);
      
      const jsSizeKB = (jsSize / 1024).toFixed(2);
      const cssSizeKB = (cssSize / 1024).toFixed(2);
      const totalSizeKB = (totalSize / 1024).toFixed(2);
      
      if (jsSize < 300 * 1024) {
        pass(`JS 大小: ${jsSizeKB}KB (目标 < 300KB)`);
      } else if (jsSize < 500 * 1024) {
        warn(`JS 大小: ${jsSizeKB}KB (警告: > 300KB)`);
      } else {
        error(`JS 大小: ${jsSizeKB}KB (过大: > 500KB)`);
      }
      
      if (cssSize < 100 * 1024) {
        pass(`CSS 大小: ${cssSizeKB}KB (目标 < 100KB)`);
      } else {
        warn(`CSS 大小: ${cssSizeKB}KB (过大)`);
      }
      
      log(`  总计: ${totalSizeKB}KB`, 'blue');
    } catch (e) {
      warn('无法计算构建大小', e.message);
    }
  },

  // 8. 性能预算检查
  performanceBudget() {
    log('\n💰 Performance Budget', 'bright');
    
    const budgetFile = path.join('src', 'config', 'performance.ts');
    if (fs.existsSync(budgetFile)) {
      pass('性能预算配置存在');
    } else {
      warn('性能预算配置不存在', '创建 src/config/performance.ts');
    }
  },
};

// 生成报告
function generateReport() {
  log('\n' + '='.repeat(60), 'bright');
  log('Performance Optimization Report', 'bright');
  log('='.repeat(60), 'bright');
  
  log(`\n✓ Passed: ${results.passed.length}`, 'green');
  log(`⚠ Warnings: ${results.warnings.length}`, 'yellow');
  log(`✗ Errors: ${results.errors.length}`, 'red');
  
  if (results.warnings.length > 0) {
    log('\n⚠ Warnings Detail:', 'yellow');
    results.warnings.forEach((w, i) => {
      log(`  ${i + 1}. ${w.message}`, 'yellow');
      if (w.suggestion) log(`     → ${w.suggestion}`, 'blue');
    });
  }
  
  if (results.errors.length > 0) {
    log('\n✗ Errors Detail:', 'red');
    results.errors.forEach((e, i) => {
      log(`  ${i + 1}. ${e.message}`, 'red');
      if (e.suggestion) log(`     → ${e.suggestion}`, 'blue');
    });
  }
  
  // 总体评估
  log('\n' + '='.repeat(60), 'bright');
  const score = results.passed.length / (results.passed.length + results.warnings.length + results.errors.length) * 100;
  
  if (score >= 90) {
    log(`🎉 优秀! 优化评分: ${score.toFixed(1)}%`, 'green');
    log('系统性能优化程度很高，继续保持!', 'green');
  } else if (score >= 70) {
    log(`👍 良好! 优化评分: ${score.toFixed(1)}%`, 'yellow');
    log('还有一些优化空间，建议处理警告项。', 'yellow');
  } else {
    log(`⚠ 需要改进! 优化评分: ${score.toFixed(1)}%`, 'red');
    log('请优先处理错误项，然后处理警告项。', 'red');
  }
  
  // 优化建议
  log('\n📋 Quick Actions:', 'bright');
  if (!fs.existsSync('dist')) {
    log('  1. 运行 npm run build 生成构建产物');
  }
  log('  2. 运行 npm run perf:lighthouse 执行性能审计');
  log('  3. 运行 npm run bundle:analyze 分析构建产物');
  log('  4. 查看 PERFORMANCE-OPTIMIZATION.md 获取详细指南');
  
  log('\n');
}

// 主函数
async function main() {
  log('\n🔍 FormalMath Interactive - Performance Optimization Check\n', 'bright');
  
  try {
    checks.buildConfig();
    checks.performanceTools();
    checks.serverConfig();
    checks.imageOptimization();
    checks.dependencies();
    checks.scripts();
    await checks.bundleSize();
    checks.performanceBudget();
    
    generateReport();
  } catch (error) {
    log(`\n检查过程中出现错误: ${error.message}`, 'red');
    process.exit(1);
  }
}

main();
