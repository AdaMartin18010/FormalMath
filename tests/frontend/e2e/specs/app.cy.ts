/// <reference types="cypress" />

describe('应用程序基本功能', () => {
  beforeEach(() => {
    cy.visit('/')
  })

  it('应该正确加载应用首页', () => {
    cy.get('header').should('be.visible')
    cy.get('main').should('be.visible')
    cy.get('footer').should('be.visible')
  })

  it('应该显示正确的标题', () => {
    cy.title().should('contain', 'FormalMath')
  })

  it('导航菜单应该正常工作', () => {
    cy.get('[data-testid="nav-menu"]').should('be.visible')
    cy.get('[data-testid="nav-menu"] a').should('have.length.at.least', 1)
  })

  it('响应式布局应该在不同视口下正确显示', () => {
    // 桌面视图
    cy.viewport(1280, 720)
    cy.get('[data-testid="sidebar"]').should('be.visible')
    
    // 平板视图
    cy.viewport(768, 1024)
    cy.get('[data-testid="sidebar"]').should('not.be.visible')
    
    // 移动视图
    cy.viewport(375, 667)
    cy.get('[data-testid="mobile-menu"]').should('be.visible')
  })
})

describe('知识图谱功能', () => {
  beforeEach(() => {
    cy.visit('/knowledge-graph')
    cy.waitForGraphReady()
  })

  it('应该加载知识图谱', () => {
    cy.get('[data-testid="knowledge-graph"]').should('be.visible')
    cy.get('[data-testid="graph-node"]').should('have.length.at.least', 1)
  })

  it('点击节点应该显示详情面板', () => {
    cy.get('[data-testid="graph-node"]').first().click()
    cy.get('[data-testid="node-detail-panel"]').should('be.visible')
    cy.get('[data-testid="node-title"]').should('not.be.empty')
  })

  it('搜索功能应该工作正常', () => {
    cy.get('[data-testid="search-input"]').type('群论')
    cy.get('[data-testid="search-results"]').should('be.visible')
    cy.get('[data-testid="search-result-item"]').should('have.length.at.least', 1)
  })

  it('缩放控制应该工作正常', () => {
    cy.get('[data-testid="zoom-in"]').click()
    cy.get('[data-testid="knowledge-graph"]').should('have.attr', 'data-zoom', 'in')
    
    cy.get('[data-testid="zoom-out"]').click()
    cy.get('[data-testid="knowledge-graph"]').should('have.attr', 'data-zoom', 'out')
    
    cy.get('[data-testid="zoom-reset"]').click()
    cy.get('[data-testid="knowledge-graph"]').should('have.attr', 'data-zoom', 'reset')
  })
})

describe('AI助手功能', () => {
  beforeEach(() => {
    cy.visit('/')
    cy.get('[data-testid="ai-assistant-toggle"]').click()
  })

  it('应该打开AI助手面板', () => {
    cy.get('[data-testid="ai-assistant-panel"]').should('be.visible')
  })

  it('应该能够发送消息', () => {
    const message = '什么是群论？'
    cy.get('[data-testid="message-input"]').type(message)
    cy.get('[data-testid="send-button"]').click()
    
    cy.get('[data-testid="user-message"]').should('contain', message)
    cy.get('[data-testid="ai-message"]', { timeout: 10000 }).should('be.visible')
  })

  it('应该支持Markdown渲染', () => {
    cy.get('[data-testid="message-input"]').type('解释定理')
    cy.get('[data-testid="send-button"]').click()
    
    cy.get('[data-testid="ai-message"] .markdown-body', { timeout: 10000 })
      .should('be.visible')
  })
})

describe('协作功能', () => {
  beforeEach(() => {
    cy.login('test@example.com', 'password')
    cy.visit('/collaboration')
  })

  it('应该显示协作用户列表', () => {
    cy.get('[data-testid="user-presence"]').should('be.visible')
  })

  it('应该能够发送协作消息', () => {
    const message = '测试协作消息'
    cy.get('[data-testid="chat-input"]').type(message)
    cy.get('[data-testid="chat-send"]').click()
    
    cy.get('[data-testid="chat-message"]').should('contain', message)
  })
})

describe('性能测试', () => {
  it('首页应该在3秒内加载完成', () => {
    cy.visit('/', {
      onBeforeLoad: (win) => {
        win.performance.mark('start-loading')
      },
      onLoad: (win) => {
        win.performance.mark('end-loading')
        win.performance.measure('page-load', 'start-loading', 'end-loading')
      }
    })
    
    cy.window().then((win) => {
      const entries = win.performance.getEntriesByName('page-load')
      const measure = entries[0]
      expect(measure.duration).to.be.lessThan(3000)
    })
  })

  it('知识图谱渲染应该在5秒内完成', () => {
    cy.visit('/knowledge-graph')
    const startTime = performance.now()
    
    cy.get('[data-testid="knowledge-graph"]', { timeout: 5000 }).should('be.visible')
    
    cy.window().then(() => {
      const endTime = performance.now()
      expect(endTime - startTime).to.be.lessThan(5000)
    })
  })
})
