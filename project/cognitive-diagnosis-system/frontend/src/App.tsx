import { BrowserRouter as Router, Routes, Route } from 'react-router-dom'
import { Layout } from 'antd'
import AppHeader from './components/layout/AppHeader'
import Dashboard from './pages/Dashboard'
import Diagnosis from './pages/Diagnosis'
import Report from './pages/Report'
import LearningPath from './pages/LearningPath'
import Profile from './pages/Profile'

const { Content } = Layout

function App() {
  return (
    <Router>
      <Layout className="min-h-screen">
        <AppHeader />
        <Content className="p-6">
          <Routes>
            <Route path="/" element={<Dashboard />} />
            <Route path="/diagnosis" element={<Diagnosis />} />
            <Route path="/report/:testId?" element={<Report />} />
            <Route path="/learning-path" element={<LearningPath />} />
            <Route path="/profile" element={<Profile />} />
          </Routes>
        </Content>
      </Layout>
    </Router>
  )
}

export default App
