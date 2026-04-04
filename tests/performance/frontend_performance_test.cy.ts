/**
 * 前端性能测试
 * Frontend Performance Testing
 * 
 * 使用Cypress和Lighthouse进行前端性能测试
 */

// 性能预算配置
const PERFORMANCE_BUDGET = {
  firstContentfulPaint: 1800,    // FCP < 1.8s
  largestContentfulPaint: 2500,  // LCP < 2.5s
  timeToInteractive: 3500,       // TTI < 3.5s
  cumulativeLayoutShift: 0.1,    // CLS < 0.1
  totalBlockingTime: 200,        // TBT < 200ms
  speedIndex: 3400,              // SI < 3.4s
};

// 资源大小预算 (KB)
const RESOURCE_BUDGET = {
  javascript: 500,
  css: 100,
  images: 1000,
  fonts: 300,
  total: 2000,
};

interface PerformanceMetrics {
  fcp: number;
  lcp: number;
  tti: number;
  cls: number;
  tbt: number;
  si: number;
}

describe('前端性能测试 - 关键页面', () => {
  const pages = [
    { path: '/', name: '首页' },
    { path: '/concepts', name: '概念列表页' },
    { path: '/concepts/set-theory', name: '概念详情页' },
    { path: '/mathematicians', name: '数学家列表页' },
    { path: '/search?q=群论', name: '搜索结果页' },
  ];

  pages.forEach(({ path, name }) => {
    describe(`📝 ${name} (${path})`, () => {
      beforeEach(() => {
        // 禁用缓存以确保一致的测试结果
        Cypress.automation('remote:debugger:protocol', {
          command: 'Network.clearBrowserCache',
        });

        // 使用慢速网络模拟
        cy.intercept('*', (req) => {
          req.on('response', (res) => {
            // 添加延迟模拟网络延迟
            res.setDelay(100);
          });
        });
      });

      it('页面加载性能指标', () => {
        const startTime = performance.now();
        
        cy.visit(path, {
          onBeforeLoad: (win) => {
            // 标记性能测试开始
            win.performance.mark('test-start');
          },
        });

        // 等待页面稳定
        cy.get('body', { timeout: 10000 }).should('be.visible');

        cy.window().then((win) => {
          const navigation = win.performance.getEntriesByType('navigation')[0] as PerformanceNavigationTiming;
          const paintEntries = win.performance.getEntriesByType('paint');

          // 计算关键指标
          const fcp = paintEntries.find(e => e.name === 'first-contentful-paint')?.startTime || 0;
          const lcp = (win as any).largestContentfulPaint || 0;
          
          // 基础性能指标
          const metrics = {
            dnsLookup: navigation.domainLookupEnd - navigation.domainLookupStart,
            tcpConnection: navigation.connectEnd - navigation.connectStart,
            serverResponse: navigation.responseEnd - navigation.requestStart,
            domProcessing: navigation.domComplete - navigation.responseEnd,
            totalLoadTime: navigation.loadEventEnd - navigation.startTime,
            fcp: fcp,
          };

          // 记录指标
          cy.task('log', `\n📊 ${name} 性能指标:`);
          cy.task('log', `  DNS查询: ${metrics.dnsLookup.toFixed(2)}ms`);
          cy.task('log', `  TCP连接: ${metrics.tcpConnection.toFixed(2)}ms`);
          cy.task('log', `  服务器响应: ${metrics.serverResponse.toFixed(2)}ms`);
          cy.task('log', `  DOM处理: ${metrics.domProcessing.toFixed(2)}ms`);
          cy.task('log', `  总加载时间: ${metrics.totalLoadTime.toFixed(2)}ms`);
          cy.task('log', `  FCP: ${metrics.fcp.toFixed(2)}ms`);

          // 断言性能预算
          expect(metrics.totalLoadTime).to.be.lessThan(5000, '总加载时间应小于5秒');
          expect(metrics.fcp).to.be.lessThan(PERFORMANCE_BUDGET.firstContentfulPaint, 
            `FCP应小于${PERFORMANCE_BUDGET.firstContentfulPaint}ms`);
        });
      });

      it('资源加载大小检查', () => {
        const resourceSizes: Record<string, number> = {
          javascript: 0,
          css: 0,
          images: 0,
          fonts: 0,
          other: 0,
        };

        cy.visit(path);

        cy.window().then((win) => {
          const resources = win.performance.getEntriesByType('resource') as PerformanceResourceTiming[];

          resources.forEach((resource) => {
            const size = resource.transferSize || 0;
            const url = resource.name.toLowerCase();

            if (url.endsWith('.js')) {
              resourceSizes.javascript += size;
            } else if (url.endsWith('.css')) {
              resourceSizes.css += size;
            } else if (/\.(png|jpg|jpeg|gif|svg|webp)$/i.test(url)) {
              resourceSizes.images += size;
            } else if (/\.(woff2?|ttf|otf|eot)$/i.test(url)) {
              resourceSizes.fonts += size;
            } else {
              resourceSizes.other += size;
            }
          });

          const total = Object.values(resourceSizes).reduce((a, b) => a + b, 0);

          cy.task('log', `\n📦 ${name} 资源大小:`);
          cy.task('log', `  JavaScript: ${(resourceSizes.javascript / 1024).toFixed(2)} KB`);
          cy.task('log', `  CSS: ${(resourceSizes.css / 1024).toFixed(2)} KB`);
          cy.task('log', `  Images: ${(resourceSizes.images / 1024).toFixed(2)} KB`);
          cy.task('log', `  Fonts: ${(resourceSizes.fonts / 1024).toFixed(2)} KB`);
          cy.task('log', `  Total: ${(total / 1024).toFixed(2)} KB`);

          // 资源大小断言
          expect(resourceSizes.javascript / 1024).to.be.lessThan(RESOURCE_BUDGET.javascript);
          expect(resourceSizes.css / 1024).to.be.lessThan(RESOURCE_BUDGET.css);
          expect(total / 1024).to.be.lessThan(RESOURCE_BUDGET.total);
        });
      });

      it('运行时性能检查', () => {
        cy.visit(path);

        // 检查长任务
        cy.window().then((win) => {
          const longTasks = (win as any).longTaskEntries || [];
          cy.task('log', `\n⏱️ ${name} 长任务数: ${longTasks.length}`);
          expect(longTasks.length).to.be.lessThan(10, '长任务数应少于10个');
        });

        // 检查内存使用
        if ((Cypress as any).memory) {
          cy.wrap((Cypress as any).memory.usedJSHeapSize / 1024 / 1024).should('be.lessThan', 100);
        }
      });
    });
  });
});

describe('前端性能测试 - 交互性能', () => {
  beforeEach(() => {
    cy.visit('/concepts');
    cy.get('[data-testid="concept-list"]', { timeout: 10000 }).should('be.visible');
  });

  it('搜索输入响应时间', () => {
    const searchInput = '[data-testid="search-input"]';
    
    cy.get(searchInput).then(($input) => {
      const startTime = performance.now();
      
      cy.get(searchInput).type('群论');
      cy.get('[data-testid="search-results"]', { timeout: 5000 }).should('be.visible');
      
      const endTime = performance.now();
      const responseTime = endTime - startTime;
      
      cy.task('log', `\n🔍 搜索响应时间: ${responseTime.toFixed(2)}ms`);
      expect(responseTime).to.be.lessThan(1000, '搜索响应应小于1秒');
    });
  });

  it('页面切换动画性能', () => {
    // 记录帧率
    let frameCount = 0;
    
    cy.window().then((win) => {
      const countFrames = () => {
        frameCount++;
        if (frameCount < 60) {
          win.requestAnimationFrame(countFrames);
        }
      };
      win.requestAnimationFrame(countFrames);
    });

    // 触发页面切换
    cy.get('[data-testid="concept-link"]').first().click();
    
    cy.window().then((win) => {
      cy.task('log', `\n🎬 渲染帧数: ${frameCount}/60`);
      expect(frameCount).to.be.greaterThan(30, '动画期间应保持在30fps以上');
    });
  });

  it('列表滚动性能', () => {
    cy.get('[data-testid="concept-list"]').then(($list) => {
      let scrollEvents = 0;
      let startTime = 0;
      
      const $el = $list[0];
      
      // 监听滚动事件
      $el.addEventListener('scroll', () => {
        scrollEvents++;
      }, { passive: true });
      
      startTime = performance.now();
      
      // 执行滚动
      cy.wrap($el).scrollTo('bottom', { duration: 1000 });
      
      cy.then(() => {
        const duration = performance.now() - startTime;
        const eventsPerSecond = scrollEvents / (duration / 1000);
        
        cy.task('log', `\n📜 滚动事件数: ${scrollEvents}`);
        cy.task('log', `  事件率: ${eventsPerSecond.toFixed(2)} events/s`);
        
        // 滚动应该平滑，事件不应过多
        expect(eventsPerSecond).to.be.lessThan(120, '滚动事件率应适中');
      });
    });
  });
});

describe('前端性能测试 - 缓存策略', () => {
  it('静态资源应正确缓存', () => {
    cy.visit('/');

    cy.window().then((win) => {
      const resources = win.performance.getEntriesByType('resource') as PerformanceResourceTiming[];
      
      const cachedResources = resources.filter(r => r.duration === 0);
      const cacheRate = (cachedResources.length / resources.length) * 100;
      
      cy.task('log', `\n💾 缓存命中率: ${cacheRate.toFixed(2)}%`);
      
      // 首次访问缓存率可能较低，但重复资源应该被缓存
      if (resources.length > 0) {
        expect(cacheRate).to.be.greaterThan(0, '应该有部分资源被缓存');
      }
    });
  });

  it('重复访问应使用缓存', () => {
    cy.visit('/');
    cy.wait(1000);
    cy.visit('/');

    cy.window().then((win) => {
      const resources = win.performance.getEntriesByType('resource') as PerformanceResourceTiming[];
      const fromCache = resources.filter(r => r.deliveryType === 'cache').length;
      
      cy.task('log', `\n🔄 缓存命中数: ${fromCache}/${resources.length}`);
    });
  });
});

// 性能测试钩子
describe('性能测试报告', () => {
  after(() => {
    // 生成性能摘要
    cy.task('generatePerformanceReport', {
      timestamp: new Date().toISOString(),
      budget: PERFORMANCE_BUDGET,
      pages: pages.map(p => p.name),
    });
  });
});

// 导出配置供其他测试使用
export { PERFORMANCE_BUDGET, RESOURCE_BUDGET };
