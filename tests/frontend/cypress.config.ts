import { defineConfig } from 'cypress'

export default defineConfig({
  // E2E测试配置
  e2e: {
    baseUrl: 'http://localhost:3000',
    supportFile: 'e2e/support/e2e.ts',
    specPattern: 'e2e/specs/**/*.cy.{ts,tsx}',
    fixturesFolder: 'e2e/fixtures',
    screenshotsFolder: 'e2e/screenshots',
    videosFolder: 'e2e/videos',
    downloadsFolder: 'e2e/downloads',
    
    // 视口设置
    viewportWidth: 1280,
    viewportHeight: 720,
    
    // 超时设置
    defaultCommandTimeout: 10000,
    pageLoadTimeout: 30000,
    requestTimeout: 10000,
    responseTimeout: 10000,
    
    // 重试设置
    retries: {
      runMode: 2,
      openMode: 0
    },
    
    // 视频录制
    video: true,
    videoCompression: 32,
    
    // 截图
    screenshotOnRunFailure: true,
    
    // 环境变量
    env: {
      apiUrl: 'http://localhost:8000',
      coverage: false
    },
    
    setupNodeEvents(on, config) {
      // 注册插件
      on('task', {
        log(message) {
          console.log(message)
          return null
        },
        table(message) {
          console.table(message)
          return null
        }
      })
      
      // 代码覆盖率插件
      if (config.env.coverage) {
        require('@cypress/code-coverage/task')(on, config)
      }
      
      return config
    }
  },
  
  // 组件测试配置
  component: {
    devServer: {
      framework: 'react',
      bundler: 'vite',
      viteConfig: {
        configFile: '../../FormalMath-Interactive/vite.config.ts'
      }
    },
    supportFile: 'e2e/support/component.ts',
    specPattern: 'unit/**/*.cy.{ts,tsx}',
    indexHtmlFile: 'e2e/support/component-index.html'
  }
});
