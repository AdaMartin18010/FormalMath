// Cypress E2E测试支持文件
import './commands'

// 全局测试钩子
before(() => {
  // 在测试套件运行前执行
  cy.log('开始E2E测试套件')
})

after(() => {
  // 在测试套件运行后执行
  cy.log('E2E测试套件完成')
})

beforeEach(() => {
  // 在每个测试用例前执行
  cy.clearLocalStorage()
  cy.clearCookies()
})

// 处理未捕获的异常
Cypress.on('uncaught:exception', (err, runnable) => {
  // 防止测试失败
  console.error('未捕获的异常:', err.message)
  return false
})

// 记录测试失败
Cypress.on('fail', (error, runnable) => {
  cy.screenshot(`failure-${Date.now()}`, { capture: 'fullPage' })
  throw error
})
