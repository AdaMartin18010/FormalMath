// Cypress自定义命令

// 登录命令
declare global {
  namespace Cypress {
    interface Chainable {
      login(email: string, password: string): Chainable<void>
      logout(): Chainable<void>
      mockApi(method: string, url: string, response: unknown): Chainable<void>
      waitForGraphReady(): Chainable<void>
      checkAccessibility(): Chainable<void>
    }
  }
}

Cypress.Commands.add('login', (email: string, password: string) => {
  cy.session([email, password], () => {
    cy.request('POST', `${Cypress.env('apiUrl')}/auth/login`, {
      email,
      password
    }).then((response) => {
      window.localStorage.setItem('token', response.body.token)
      window.localStorage.setItem('user', JSON.stringify(response.body.user))
    })
  })
})

Cypress.Commands.add('logout', () => {
  cy.request('POST', `${Cypress.env('apiUrl')}/auth/logout`)
  cy.clearLocalStorage()
  cy.clearCookies()
})

Cypress.Commands.add('mockApi', (method: string, url: string, response: unknown) => {
  cy.intercept(method, url, {
    statusCode: 200,
    body: response
  }).as('apiMock')
})

Cypress.Commands.add('waitForGraphReady', () => {
  cy.get('[data-testid="knowledge-graph"]', { timeout: 10000 })
    .should('be.visible')
    .and('have.attr', 'data-ready', 'true')
})

// 无障碍测试命令
Cypress.Commands.add('checkAccessibility', () => {
  cy.injectAxe()
  cy.checkA11y(null, {
    runOnly: {
      type: 'tag',
      values: ['wcag2a', 'wcag2aa']
    }
  })
})
