#!/usr/bin/env python3
"""
多语言扩展脚本
为299个概念添加俄语、意大利语、西班牙语、葡萄牙语的Wikipedia链接和名称
"""

import yaml
import json
from typing import Dict, List, Any

# 语言代码映射
LANGUAGE_CODES = {
    'en': 'English',
    'de': 'Deutsch', 
    'fr': 'Français',
    'ja': '日本語',
    'ru': 'Русский',
    'it': 'Italiano',
    'es': 'Español',
    'pt': 'Português'
}

# 各语言Wikipedia域名
WIKI_DOMAINS = {
    'en': 'en.wikipedia.org',
    'de': 'de.wikipedia.org',
    'fr': 'fr.wikipedia.org',
    'ja': 'ja.wikipedia.org',
    'ru': 'ru.wikipedia.org',
    'it': 'it.wikipedia.org',
    'es': 'es.wikipedia.org',
    'pt': 'pt.wikipedia.org'
}

# 核心概念的多语言翻译映射
# 基于数学术语的标准翻译
CONCEPT_TRANSLATIONS = {
    # 分析学
    'limit': {
        'ru': {'title': 'Предел (математика)', 'url': 'https://ru.wikipedia.org/wiki/Предел_(математика)'},
        'it': {'title': 'Limite (matematica)', 'url': 'https://it.wikipedia.org/wiki/Limite_(matematica)'},
        'es': {'title': 'Límite matemático', 'url': 'https://es.wikipedia.org/wiki/Límite_matemático'},
        'pt': {'title': 'Limite (matemática)', 'url': 'https://pt.wikipedia.org/wiki/Limite_(matemática)'}
    },
    'continuity': {
        'ru': {'title': 'Непрерывная функция', 'url': 'https://ru.wikipedia.org/wiki/Непрерывная_функция'},
        'it': {'title': 'Funzione continua', 'url': 'https://it.wikipedia.org/wiki/Funzione_continua'},
        'es': {'title': 'Función continua', 'url': 'https://es.wikipedia.org/wiki/Función_continua'},
        'pt': {'title': 'Função contínua', 'url': 'https://pt.wikipedia.org/wiki/Função_contínua'}
    },
    'derivative': {
        'ru': {'title': 'Производная функции', 'url': 'https://ru.wikipedia.org/wiki/Производная_функции'},
        'it': {'title': 'Derivata', 'url': 'https://it.wikipedia.org/wiki/Derivata'},
        'es': {'title': 'Derivada', 'url': 'https://es.wikipedia.org/wiki/Derivada'},
        'pt': {'title': 'Derivada', 'url': 'https://pt.wikipedia.org/wiki/Derivada'}
    },
    'integral': {
        'ru': {'title': 'Интеграл', 'url': 'https://ru.wikipedia.org/wiki/Интеграл'},
        'it': {'title': 'Integrale', 'url': 'https://it.wikipedia.org/wiki/Integrale'},
        'es': {'title': 'Integral', 'url': 'https://es.wikipedia.org/wiki/Integral'},
        'pt': {'title': 'Integral', 'url': 'https://pt.wikipedia.org/wiki/Integral'}
    },
    'sequence': {
        'ru': {'title': 'Последовательность', 'url': 'https://ru.wikipedia.org/wiki/Последовательность'},
        'it': {'title': 'Successione (matematica)', 'url': 'https://it.wikipedia.org/wiki/Successione_(matematica)'},
        'es': {'title': 'Sucesión matemática', 'url': 'https://es.wikipedia.org/wiki/Sucesión_matemática'},
        'pt': {'title': 'Sequência', 'url': 'https://pt.wikipedia.org/wiki/Sequência'}
    },
    'series': {
        'ru': {'title': 'Ряд (математика)', 'url': 'https://ru.wikipedia.org/wiki/Ряд_(математика)'},
        'it': {'title': 'Serie (matematica)', 'url': 'https://it.wikipedia.org/wiki/Serie_(matematica)'},
        'es': {'title': 'Serie matemática', 'url': 'https://es.wikipedia.org/wiki/Serie_matemática'},
        'pt': {'title': 'Série (matemática)', 'url': 'https://pt.wikipedia.org/wiki/Série_(matemática)'}
    },
    'convergence': {
        'ru': {'title': 'Сходимость', 'url': 'https://ru.wikipedia.org/wiki/Сходимость'},
        'it': {'title': 'Convergenza', 'url': 'https://it.wikipedia.org/wiki/Convergenza'},
        'es': {'title': 'Convergencia (matemática)', 'url': 'https://es.wikipedia.org/wiki/Convergencia_(matemática)'},
        'pt': {'title': 'Convergência (matemática)', 'url': 'https://pt.wikipedia.org/wiki/Convergência_(matemática)'}
    },
    'uniform_convergence': {
        'ru': {'title': 'Равномерная сходимость', 'url': 'https://ru.wikipedia.org/wiki/Равномерная_сходимость'},
        'it': {'title': 'Convergenza uniforme', 'url': 'https://it.wikipedia.org/wiki/Convergenza_uniforme'},
        'es': {'title': 'Convergencia uniforme', 'url': 'https://es.wikipedia.org/wiki/Convergencia_uniforme'},
        'pt': {'title': 'Convergência uniforme', 'url': 'https://pt.wikipedia.org/wiki/Convergência_uniforme'}
    },
    
    # 线性代数
    'vector_space': {
        'ru': {'title': 'Векторное пространство', 'url': 'https://ru.wikipedia.org/wiki/Векторное_пространство'},
        'it': {'title': 'Spazio vettoriale', 'url': 'https://it.wikipedia.org/wiki/Spazio_vettoriale'},
        'es': {'title': 'Espacio vectorial', 'url': 'https://es.wikipedia.org/wiki/Espacio_vectorial'},
        'pt': {'title': 'Espaço vetorial', 'url': 'https://pt.wikipedia.org/wiki/Espaço_vetorial'}
    },
    'linear_transformation': {
        'ru': {'title': 'Линейное отображение', 'url': 'https://ru.wikipedia.org/wiki/Линейное_отображение'},
        'it': {'title': 'Applicazione lineare', 'url': 'https://it.wikipedia.org/wiki/Applicazione_lineare'},
        'es': {'title': 'Transformación lineal', 'url': 'https://es.wikipedia.org/wiki/Transformación_lineal'},
        'pt': {'title': 'Transformação linear', 'url': 'https://pt.wikipedia.org/wiki/Transformação_linear'}
    },
    'matrix': {
        'ru': {'title': 'Матрица (математика)', 'url': 'https://ru.wikipedia.org/wiki/Матрица_(математика)'},
        'it': {'title': 'Matrice', 'url': 'https://it.wikipedia.org/wiki/Matrice'},
        'es': {'title': 'Matriz (matemáticas)', 'url': 'https://es.wikipedia.org/wiki/Matriz_(matemáticas)'},
        'pt': {'title': 'Matriz (matemática)', 'url': 'https://pt.wikipedia.org/wiki/Matriz_(matemática)'}
    },
    'eigenvalue': {
        'ru': {'title': 'Собственное значение', 'url': 'https://ru.wikipedia.org/wiki/Собственное_значение'},
        'it': {'title': 'Autovalore e autovettore', 'url': 'https://it.wikipedia.org/wiki/Autovalore_e_autovettore'},
        'es': {'title': 'Valor propio', 'url': 'https://es.wikipedia.org/wiki/Valor_propio'},
        'pt': {'title': 'Valor próprio', 'url': 'https://pt.wikipedia.org/wiki/Valor_próprio'}
    },
    'inner_product': {
        'ru': {'title': 'Скалярное произведение', 'url': 'https://ru.wikipedia.org/wiki/Скалярное_произведение'},
        'it': {'title': 'Prodotto scalare', 'url': 'https://it.wikipedia.org/wiki/Prodotto_scalare'},
        'es': {'title': 'Producto escalar', 'url': 'https://es.wikipedia.org/wiki/Producto_escalar'},
        'pt': {'title': 'Produto escalar', 'url': 'https://pt.wikipedia.org/wiki/Produto_escalar'}
    },
    
    # 抽象代数
    'group': {
        'ru': {'title': 'Группа (математика)', 'url': 'https://ru.wikipedia.org/wiki/Группа_(математика)'},
        'it': {'title': 'Gruppo (algebra)', 'url': 'https://it.wikipedia.org/wiki/Gruppo_(algebra)'},
        'es': {'title': 'Grupo (matemáticas)', 'url': 'https://es.wikipedia.org/wiki/Grupo_(matemáticas)'},
        'pt': {'title': 'Grupo (matemática)', 'url': 'https://pt.wikipedia.org/wiki/Grupo_(matemática)'}
    },
    'ring': {
        'ru': {'title': 'Кольцо (математика)', 'url': 'https://ru.wikipedia.org/wiki/Кольцо_(математика)'},
        'it': {'title': 'Anello (algebra)', 'url': 'https://it.wikipedia.org/wiki/Anello_(algebra)'},
        'es': {'title': 'Anillo (matemática)', 'url': 'https://es.wikipedia.org/wiki/Anillo_(matemática)'},
        'pt': {'title': 'Anel (matemática)', 'url': 'https://pt.wikipedia.org/wiki/Anel_(matemática)'}
    },
    'field': {
        'ru': {'title': 'Поле (алгебра)', 'url': 'https://ru.wikipedia.org/wiki/Поле_(алгебра)'},
        'it': {'title': 'Campo (matematica)', 'url': 'https://it.wikipedia.org/wiki/Campo_(matematica)'},
        'es': {'title': 'Cuerpo (matemáticas)', 'url': 'https://es.wikipedia.org/wiki/Cuerpo_(matemáticas)'},
        'pt': {'title': 'Corpo (matemática)', 'url': 'https://pt.wikipedia.org/wiki/Corpo_(matemática)'}
    },
    'homomorphism': {
        'ru': {'title': 'Гомоморфизм', 'url': 'https://ru.wikipedia.org/wiki/Гомоморфизм'},
        'it': {'title': 'Omomorfismo', 'url': 'https://it.wikipedia.org/wiki/Omomorfismo'},
        'es': {'title': 'Homomorfismo', 'url': 'https://es.wikipedia.org/wiki/Homomorfismo'},
        'pt': {'title': 'Homomorfismo', 'url': 'https://pt.wikipedia.org/wiki/Homomorfismo'}
    },
    
    # 拓扑学
    'topology': {
        'ru': {'title': 'Топология', 'url': 'https://ru.wikipedia.org/wiki/Топология'},
        'it': {'title': 'Topologia', 'url': 'https://it.wikipedia.org/wiki/Topologia'},
        'es': {'title': 'Topología', 'url': 'https://es.wikipedia.org/wiki/Topología'},
        'pt': {'title': 'Topologia', 'url': 'https://pt.wikipedia.org/wiki/Topologia'}
    },
    'topological_space': {
        'ru': {'title': 'Топологическое пространство', 'url': 'https://ru.wikipedia.org/wiki/Топологическое_пространство'},
        'it': {'title': 'Spazio topologico', 'url': 'https://it.wikipedia.org/wiki/Spazio_topologico'},
        'es': {'title': 'Espacio topológico', 'url': 'https://es.wikipedia.org/wiki/Espacio_topológico'},
        'pt': {'title': 'Espaço topológico', 'url': 'https://pt.wikipedia.org/wiki/Espaço_topológico'}
    },
    'compactness': {
        'ru': {'title': 'Компактное пространство', 'url': 'https://ru.wikipedia.org/wiki/Компактное_пространство'},
        'it': {'title': 'Spazio compatto', 'url': 'https://it.wikipedia.org/wiki/Spazio_compatto'},
        'es': {'title': 'Espacio compacto', 'url': 'https://es.wikipedia.org/wiki/Espacio_compacto'},
        'pt': {'title': 'Espaço compacto', 'url': 'https://pt.wikipedia.org/wiki/Espaço_compacto'}
    },
    'connectedness': {
        'ru': {'title': 'Связное пространство', 'url': 'https://ru.wikipedia.org/wiki/Связное_пространство'},
        'it': {'title': 'Spazio connesso', 'url': 'https://it.wikipedia.org/wiki/Spazio_connesso'},
        'es': {'title': 'Espacio conexo', 'url': 'https://es.wikipedia.org/wiki/Espacio_conexo'},
        'pt': {'title': 'Espaço conexo', 'url': 'https://pt.wikipedia.org/wiki/Espaço_conexo'}
    },
    
    # 微分几何
    'manifold': {
        'ru': {'title': 'Многообразие', 'url': 'https://ru.wikipedia.org/wiki/Многообразие'},
        'it': {'title': 'Varietà (geometria differenziale)', 'url': 'https://it.wikipedia.org/wiki/Varietà_(geometria_differenziale)'},
        'es': {'title': 'Variedad diferenciable', 'url': 'https://es.wikipedia.org/wiki/Variedad_diferenciable'},
        'pt': {'title': 'Variedade diferenciável', 'url': 'https://pt.wikipedia.org/wiki/Variedade_diferenciável'}
    },
    'tangent_space': {
        'ru': {'title': 'Касательное пространство', 'url': 'https://ru.wikipedia.org/wiki/Касательное_пространство'},
        'it': {'title': 'Spazio tangente', 'url': 'https://it.wikipedia.org/wiki/Spazio_tangente'},
        'es': {'title': 'Espacio tangente', 'url': 'https://es.wikipedia.org/wiki/Espacio_tangente'},
        'pt': {'title': 'Espaço tangente', 'url': 'https://pt.wikipedia.org/wiki/Espaço_tangente'}
    },
    'riemannian_metric': {
        'ru': {'title': 'Риманова метрика', 'url': 'https://ru.wikipedia.org/wiki/Риманова_метрика'},
        'it': {'title': 'Metrica riemanniana', 'url': 'https://it.wikipedia.org/wiki/Metrica_riemanniana'},
        'es': {'title': 'Métrica riemanniana', 'url': 'https://es.wikipedia.org/wiki/Métrica_riemanniana'},
        'pt': {'title': 'Métrica riemanniana', 'url': 'https://pt.wikipedia.org/wiki/Métrica_riemanniana'}
    },
    
    # 概率统计
    'probability': {
        'ru': {'title': 'Теория вероятностей', 'url': 'https://ru.wikipedia.org/wiki/Теория_вероятностей'},
        'it': {'title': 'Teoria della probabilità', 'url': 'https://it.wikipedia.org/wiki/Teoria_della_probabilità'},
        'es': {'title': 'Teoría de la probabilidad', 'url': 'https://es.wikipedia.org/wiki/Teoría_de_la_probabilidad'},
        'pt': {'title': 'Teoria das probabilidades', 'url': 'https://pt.wikipedia.org/wiki/Teoria_das_probabilidades'}
    },
    'random_variable': {
        'ru': {'title': 'Случайная величина', 'url': 'https://ru.wikipedia.org/wiki/Случайная_величина'},
        'it': {'title': 'Variabile casuale', 'url': 'https://it.wikipedia.org/wiki/Variabile_casuale'},
        'es': {'title': 'Variable aleatoria', 'url': 'https://es.wikipedia.org/wiki/Variable_aleatoria'},
        'pt': {'title': 'Variável aleatória', 'url': 'https://pt.wikipedia.org/wiki/Variável_aleatória'}
    },
    'distribution': {
        'ru': {'title': 'Распределение вероятностей', 'url': 'https://ru.wikipedia.org/wiki/Распределение_вероятностей'},
        'it': {'title': 'Distribuzione di probabilità', 'url': 'https://it.wikipedia.org/wiki/Distribuzione_di_probabilità'},
        'es': {'title': 'Distribución de probabilidad', 'url': 'https://es.wikipedia.org/wiki/Distribución_de_probabilidad'},
        'pt': {'title': 'Distribuição de probabilidade', 'url': 'https://pt.wikipedia.org/wiki/Distribuição_de_probabilidade'}
    },
    'expectation': {
        'ru': {'title': 'Математическое ожидание', 'url': 'https://ru.wikipedia.org/wiki/Математическое_ожидание'},
        'it': {'title': 'Valore atteso', 'url': 'https://it.wikipedia.org/wiki/Valore_atteso'},
        'es': {'title': 'Esperanza matemática', 'url': 'https://es.wikipedia.org/wiki/Esperanza_matemática'},
        'pt': {'title': 'Esperança matemática', 'url': 'https://pt.wikipedia.org/wiki/Esperança_matemática'}
    },
    
    # 数论
    'prime_number': {
        'ru': {'title': 'Простое число', 'url': 'https://ru.wikipedia.org/wiki/Простое_число'},
        'it': {'title': 'Numero primo', 'url': 'https://it.wikipedia.org/wiki/Numero_primo'},
        'es': {'title': 'Número primo', 'url': 'https://es.wikipedia.org/wiki/Número_primo'},
        'pt': {'title': 'Número primo', 'url': 'https://pt.wikipedia.org/wiki/Número_primo'}
    },
    'congruence': {
        'ru': {'title': 'Сравнение по модулю', 'url': 'https://ru.wikipedia.org/wiki/Сравнение_по_модулю'},
        'it': {'title': 'Congruenza (aritmetica)', 'url': 'https://it.wikipedia.org/wiki/Congruenza_(aritmetica)'},
        'es': {'title': 'Congruencia (aritmética)', 'url': 'https://es.wikipedia.org/wiki/Congruencia_(aritmética)'},
        'pt': {'title': 'Congruência (aritmética)', 'url': 'https://pt.wikipedia.org/wiki/Congruência_(aritmética)'}
    },
    
    # 集合论
    'set': {
        'ru': {'title': 'Множество', 'url': 'https://ru.wikipedia.org/wiki/Множество'},
        'it': {'title': 'Insieme', 'url': 'https://it.wikipedia.org/wiki/Insieme'},
        'es': {'title': 'Conjunto', 'url': 'https://es.wikipedia.org/wiki/Conjunto'},
        'pt': {'title': 'Conjunto', 'url': 'https://pt.wikipedia.org/wiki/Conjunto'}
    },
    'function': {
        'ru': {'title': 'Функция (математика)', 'url': 'https://ru.wikipedia.org/wiki/Функция_(математика)'},
        'it': {'title': 'Funzione (matematica)', 'url': 'https://it.wikipedia.org/wiki/Funzione_(matematica)'},
        'es': {'title': 'Función matemática', 'url': 'https://es.wikipedia.org/wiki/Función_matemática'},
        'pt': {'title': 'Função (matemática)', 'url': 'https://pt.wikipedia.org/wiki/Função_(matemática)'}
    },
    
    # 逻辑
    'propositional_logic': {
        'ru': {'title': 'Исчисление высказываний', 'url': 'https://ru.wikipedia.org/wiki/Исчисление_высказываний'},
        'it': {'title': 'Logica proposizionale', 'url': 'https://it.wikipedia.org/wiki/Logica_proposizionale'},
        'es': {'title': 'Lógica proposicional', 'url': 'https://es.wikipedia.org/wiki/Lógica_proposicional'},
        'pt': {'title': 'Lógica proposicional', 'url': 'https://pt.wikipedia.org/wiki/Lógica_proposicional'}
    },
    'predicate_logic': {
        'ru': {'title': 'Логика предикатов', 'url': 'https://ru.wikipedia.org/wiki/Логика_предикатов'},
        'it': {'title': 'Logica del primo ordine', 'url': 'https://it.wikipedia.org/wiki/Logica_del_primo_ordine'},
        'es': {'title': 'Lógica de predicados', 'url': 'https://es.wikipedia.org/wiki/Lógica_de_predicados'},
        'pt': {'title': 'Lógica de predicados', 'url': 'https://pt.wikipedia.org/wiki/Lógica_de_predicados'}
    },
}

# 分类映射：将概念ID映射到翻译
def get_translation_for_concept(concept_id: str, category: str, name: str) -> Dict[str, Dict[str, str]]:
    """根据概念ID、分类和名称获取翻译"""
    
    # 直接匹配
    if concept_id in CONCEPT_TRANSLATIONS:
        return CONCEPT_TRANSLATIONS[concept_id]
    
    # 基于分类和名称生成通用翻译
    return generate_generic_translation(concept_id, category, name)

def generate_generic_translation(concept_id: str, category: str, name: str) -> Dict[str, Dict[str, str]]:
    """基于数学术语规则生成通用翻译"""
    translations = {}
    
    # 清理名称用于URL
    clean_name = name.replace(' ', '_').replace('（', '(').replace('）', ')')
    
    for lang in ['ru', 'it', 'es', 'pt']:
        # 使用英语Wikipedia标题作为基础
        en_title = concept_id.replace('_', ' ').title()
        
        # 根据语言调整标题格式
        if lang == 'ru':
            title = transliterate_to_russian(concept_id, name)
        elif lang == 'it':
            title = format_italian_title(concept_id, name)
        elif lang == 'es':
            title = format_spanish_title(concept_id, name)
        elif lang == 'pt':
            title = format_portuguese_title(concept_id, name)
        else:
            title = en_title
        
        url = f"https://{WIKI_DOMAINS[lang]}/wiki/{title.replace(' ', '_')}"
        
        translations[lang] = {
            'title': title,
            'url': url
        }
    
    return translations

def transliterate_to_russian(concept_id: str, name: str) -> str:
    """将概念名称转换为俄语形式"""
    # 常见数学术语的俄语映射
    russian_terms = {
        'limit': 'Предел (математика)',
        'continuity': 'Непрерывность',
        'derivative': 'Производная',
        'integral': 'Интеграл',
        'function': 'Функция (математика)',
        'sequence': 'Последовательность',
        'series': 'Ряд (математика)',
        'convergence': 'Сходимость',
        'vector': 'Вектор',
        'matrix': 'Матрица (математика)',
        'group': 'Группа (математика)',
        'ring': 'Кольцо (математика)',
        'field': 'Поле (алгебра)',
        'topology': 'Топология',
        'manifold': 'Многообразие',
        'probability': 'Теория вероятностей',
        'statistics': 'Статистика',
        'number': 'Число',
        'set': 'Множество',
        'logic': 'Логика',
        'proof': 'Доказательство (математика)',
        'theorem': 'Теорема',
        'lemma': 'Лемма (математика)',
        'axiom': 'Аксиома',
        'definition': 'Определение (математика)',
    }
    
    for key, value in russian_terms.items():
        if key in concept_id.lower():
            return value
    
    return f"{name} (математика)"

def format_italian_title(concept_id: str, name: str) -> str:
    """格式化意大利语标题"""
    italian_terms = {
        'limit': 'Limite (matematica)',
        'continuity': 'Funzione continua',
        'derivative': 'Derivata',
        'integral': 'Integrale',
        'function': 'Funzione (matematica)',
        'sequence': 'Successione (matematica)',
        'series': 'Serie (matematica)',
        'convergence': 'Convergenza',
        'vector': 'Vettore',
        'matrix': 'Matrice',
        'group': 'Gruppo (algebra)',
        'ring': 'Anello (algebra)',
        'field': 'Campo (matematica)',
        'topology': 'Topologia',
        'manifold': 'Varietà (geometria differenziale)',
        'probability': 'Teoria della probabilità',
        'statistics': 'Statistica',
        'number': 'Numero',
        'set': 'Insieme',
        'logic': 'Logica',
        'proof': 'Dimostrazione matematica',
        'theorem': 'Teorema',
        'lemma': 'Lemma (matematica)',
        'axiom': 'Assioma (matematica)',
        'definition': 'Definizione (matematica)',
    }
    
    for key, value in italian_terms.items():
        if key in concept_id.lower():
            return value
    
    return f"{name} (matematica)"

def format_spanish_title(concept_id: str, name: str) -> str:
    """格式化西班牙语标题"""
    spanish_terms = {
        'limit': 'Límite matemático',
        'continuity': 'Función continua',
        'derivative': 'Derivada',
        'integral': 'Integral',
        'function': 'Función matemática',
        'sequence': 'Sucesión matemática',
        'series': 'Serie matemática',
        'convergence': 'Convergencia (matemática)',
        'vector': 'Vector',
        'matrix': 'Matriz (matemáticas)',
        'group': 'Grupo (matemáticas)',
        'ring': 'Anillo (matemática)',
        'field': 'Cuerpo (matemáticas)',
        'topology': 'Topología',
        'manifold': 'Variedad diferenciable',
        'probability': 'Teoría de la probabilidad',
        'statistics': 'Estadística',
        'number': 'Número',
        'set': 'Conjunto',
        'logic': 'Lógica',
        'proof': 'Demostración matemática',
        'theorem': 'Teorema',
        'lemma': 'Lema (matemática)',
        'axiom': 'Axioma (lógica)',
        'definition': 'Definición matemática',
    }
    
    for key, value in spanish_terms.items():
        if key in concept_id.lower():
            return value
    
    return f"{name} (matemática)"

def format_portuguese_title(concept_id: str, name: str) -> str:
    """格式化葡萄牙语标题"""
    portuguese_terms = {
        'limit': 'Limite (matemática)',
        'continuity': 'Função contínua',
        'derivative': 'Derivada',
        'integral': 'Integral',
        'function': 'Função (matemática)',
        'sequence': 'Sequência',
        'series': 'Série (matemática)',
        'convergence': 'Convergência (matemática)',
        'vector': 'Vetor',
        'matrix': 'Matriz (matemática)',
        'group': 'Grupo (matemática)',
        'ring': 'Anel (matemática)',
        'field': 'Corpo (matemática)',
        'topology': 'Topologia',
        'manifold': 'Variedade diferenciável',
        'probability': 'Teoria das probabilidades',
        'statistics': 'Estatística',
        'number': 'Número',
        'set': 'Conjunto',
        'logic': 'Lógica',
        'proof': 'Prova matemática',
        'theorem': 'Teorema',
        'lemma': 'Lema (matemática)',
        'axiom': 'Axioma',
        'definition': 'Definição (matemática)',
    }
    
    for key, value in portuguese_terms.items():
        if key in concept_id.lower():
            return value
    
    return f"{name} (matemática)"

def main():
    """主函数：读取YAML，添加多语言支持，输出扩展文件"""
    
    # 读取现有概念图谱
    with open('concept_prerequisites_multilang.yaml', 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    
    concepts = data['concepts']
    print(f"Loaded {len(concepts)} concepts")
    
    # 统计信息
    stats = {
        'total_concepts': len(concepts),
        'concepts_with_new_langs': 0,
        'languages_added': ['ru', 'it', 'es', 'pt'],
        'translations_generated': 0
    }
    
    # 术语对照表
    terminology_table = {}
    
    # 为每个概念添加新语言支持
    for concept in concepts:
        concept_id = concept['concept_id']
        name = concept['name']
        category = concept.get('category', '未知')
        
        # 确保 multilang 存在
        if 'multilang' not in concept:
            concept['multilang'] = {}
        
        # 获取翻译
        translations = get_translation_for_concept(concept_id, category, name)
        
        # 添加新语言
        added = False
        for lang in ['ru', 'it', 'es', 'pt']:
            if lang not in concept['multilang'] and lang in translations:
                concept['multilang'][lang] = translations[lang]
                stats['translations_generated'] += 1
                added = True
        
        if added:
            stats['concepts_with_new_langs'] += 1
        
        # 添加到术语对照表
        terminology_table[concept_id] = {
            'concept_id': concept_id,
            'name_zh': name,
            'category': category,
            'translations': {}
        }
        
        for lang_code, lang_info in concept['multilang'].items():
            terminology_table[concept_id]['translations'][lang_code] = {
                'title': lang_info.get('title', ''),
                'url': lang_info.get('url', '')
            }
    
    # 保存扩展后的YAML
    output_yaml = {
        'metadata': {
            'title': 'FormalMath Multilanguage Concept Graph (Extended)',
            'version': '1.1.0',
            'generated_date': '2026-04-04',
            'description': '扩展多语言支持的概念图谱（包含俄语、意大利语、西班牙语、葡萄牙语）',
            'statistics': {
                'total_concepts': len(concepts),
                'languages_supported': ['en', 'de', 'fr', 'ja', 'ru', 'it', 'es', 'pt'],
                'concepts_with_multilang': len([c for c in concepts if c.get('multilang')]),
                'new_languages_added': ['ru', 'it', 'es', 'pt']
            }
        },
        'concepts': concepts
    }
    
    with open('concept_prerequisites_multilang_extended.yaml', 'w', encoding='utf-8') as f:
        yaml.dump(output_yaml, f, allow_unicode=True, sort_keys=False, width=120)
    
    print(f"Saved extended YAML to concept_prerequisites_multilang_extended.yaml")
    
    # 保存术语对照表JSON
    with open('multilang_terminology_table.json', 'w', encoding='utf-8') as f:
        json.dump({
            'metadata': {
                'version': '1.0.0',
                'generated_date': '2026-04-04',
                'total_concepts': len(terminology_table),
                'languages': ['zh', 'en', 'de', 'fr', 'ja', 'ru', 'it', 'es', 'pt']
            },
            'terminology': terminology_table
        }, f, ensure_ascii=False, indent=2)
    
    print(f"Saved terminology table to multilang_terminology_table.json")
    
    # 打印统计
    print(f"\nStatistics:")
    print(f"  - Total concepts: {stats['total_concepts']}")
    print(f"  - Concepts with new languages: {stats['concepts_with_new_langs']}")
    print(f"  - Translations generated: {stats['translations_generated']}")
    print(f"  - Languages added: {', '.join(stats['languages_added'])}")

if __name__ == '__main__':
    main()
