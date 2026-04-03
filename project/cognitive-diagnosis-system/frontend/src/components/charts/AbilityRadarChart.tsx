import ReactECharts from 'echarts-for-react'

interface AbilityRadarChartProps {
  data: {
    L0: number
    L1: number
    L2: number
    L3: number
  }
}

function AbilityRadarChart({ data }: AbilityRadarChartProps) {
  const option = {
    radar: {
      indicator: [
        { name: 'L0\n基础概念', max: 1 },
        { name: 'L1\n定义理解', max: 1 },
        { name: 'L2\n定理应用', max: 1 },
        { name: 'L3\n综合证明', max: 1 }
      ],
      radius: '65%',
      splitNumber: 4,
      axisName: {
        color: '#666',
        fontSize: 12
      },
      splitLine: {
        lineStyle: {
          color: ['#eee']
        }
      },
      splitArea: {
        areaStyle: {
          color: ['#f8f8f8', '#fff']
        }
      }
    },
    series: [{
      type: 'radar',
      data: [{
        value: [data.L0, data.L1, data.L2, data.L3],
        name: '能力水平',
        areaStyle: {
          color: 'rgba(24, 144, 255, 0.3)'
        },
        lineStyle: {
          color: '#1890ff',
          width: 2
        },
        itemStyle: {
          color: '#1890ff'
        }
      }]
    }]
  }

  return <ReactECharts option={option} style={{ height: 280 }} />
}

export default AbilityRadarChart
