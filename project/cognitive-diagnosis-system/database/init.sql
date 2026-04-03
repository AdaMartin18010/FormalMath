-- FormalMath认知诊断系统 - 数据库初始化脚本

-- 创建数据库（需要postgres权限）
-- CREATE DATABASE formalmath_cds;

-- 连接数据库后执行
\c formalmath_cds;

-- 学生表
CREATE TABLE IF NOT EXISTS students (
    id VARCHAR(36) PRIMARY KEY,
    username VARCHAR(50) NOT NULL,
    email VARCHAR(100) UNIQUE,
    hashed_password VARCHAR(255),
    current_level INTEGER DEFAULT 0,
    learning_style VARCHAR(20),
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 题目表
CREATE TABLE IF NOT EXISTS questions (
    id VARCHAR(36) PRIMARY KEY,
    content TEXT NOT NULL,
    type VARCHAR(10) NOT NULL,
    level INTEGER NOT NULL,
    difficulty INTEGER NOT NULL,
    branch VARCHAR(50),
    concepts JSON,
    skills JSON,
    options JSON,
    answer TEXT,
    explanation TEXT,
    time_estimate INTEGER,
    score DECIMAL(5,2),
    prerequisite_concepts JSON,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 测试记录表
CREATE TABLE IF NOT EXISTS tests (
    id VARCHAR(36) PRIMARY KEY,
    student_id VARCHAR(36) REFERENCES students(id),
    test_type VARCHAR(20),
    status VARCHAR(20) DEFAULT 'pending',
    start_time TIMESTAMP,
    end_time TIMESTAMP,
    total_score DECIMAL(5,2),
    target_level INTEGER,
    focus_areas JSON,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 答题记录表
CREATE TABLE IF NOT EXISTS responses (
    id VARCHAR(36) PRIMARY KEY,
    test_id VARCHAR(36) REFERENCES tests(id),
    question_id VARCHAR(36) REFERENCES questions(id),
    answer TEXT,
    is_correct BOOLEAN,
    score DECIMAL(5,2),
    time_spent INTEGER,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 诊断结果表
CREATE TABLE IF NOT EXISTS diagnosis_results (
    id VARCHAR(36) PRIMARY KEY,
    student_id VARCHAR(36) REFERENCES students(id),
    test_id VARCHAR(36) REFERENCES tests(id),
    knowledge_state JSON,
    ability_level JSON,
    weak_areas JSON,
    strong_areas JSON,
    suggestions JSON,
    confidence DECIMAL(3,2),
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 学习路径表
CREATE TABLE IF NOT EXISTS learning_paths (
    id VARCHAR(36) PRIMARY KEY,
    student_id VARCHAR(36) REFERENCES students(id),
    diagnosis_id VARCHAR(36) REFERENCES diagnosis_results(id),
    path_data JSON,
    current_node VARCHAR(36),
    progress DECIMAL(5,2) DEFAULT 0.0,
    created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- 创建索引
CREATE INDEX idx_students_email ON students(email);
CREATE INDEX idx_questions_level ON questions(level);
CREATE INDEX idx_questions_branch ON questions(branch);
CREATE INDEX idx_tests_student ON tests(student_id);
CREATE INDEX idx_responses_test ON responses(test_id);
CREATE INDEX idx_diagnosis_student ON diagnosis_results(student_id);

-- 插入示例数据
INSERT INTO students (id, username, email, current_level) VALUES
('student-001', '张三', 'zhangsan@example.com', 2),
('student-002', '李四', 'lisi@example.com', 1);

-- 插入示例题目（部分）
INSERT INTO questions (id, content, type, level, difficulty, branch, concepts, answer, explanation, time_estimate, score) VALUES
('CDS-L0-A-001', '下列哪个集合与运算构成群？A. 自然数集 ℕ 与加法运算 B. 整数集 ℤ 与加法运算 C. 整数集 ℤ 与乘法运算 D. 偶数集 2ℤ 与乘法运算', 'SC', 0, 1, '代数学', '["群", "代数结构"]', 'B', '整数加法是群（单位元0，逆元是相反数）。', 60, 5),
('CDS-L0-AN-001', '数列极限 lim(n→∞) aₙ = a 的直观含义是什么？A. 数列的项最终会等于a B. 数列的项会无限接近a C. 数列的每一项都小于a D. 数列单调递减趋向a', 'SC', 0, 1, '分析学', '["极限", "数列"]', 'B', '极限的直观含义是"无限接近但不一定达到"。', 60, 5),
('CDS-L1-A-001', '验证 (ℤ₅, +) 是否构成群，需要验证哪些条件？A. 只需验证加法封闭 B. 验证封闭性、结合律、单位元、逆元 C. 只需验证交换律 D. 验证加法和乘法', 'SC', 1, 2, '代数学', '["群", "群公理"]', 'B', '群的四个公理：封闭性、结合律、单位元、逆元。', 90, 5);
