# FormalMath 课堂验证 A/B 测试随机分组脚本
# 用法: powershell -File A-B测试分组脚本.ps1 -InputFile students.csv -OutputFile groups.csv

param(
    [string]$InputFile = "students.csv",
    [string]$OutputFile = "groups.csv",
    [int]$GroupSize = 15
)

$Students = Import-Csv $InputFile
$Shuffled = $Students | Sort-Object { Get-Random }
$Exp = $Shuffled | Select-Object -First $GroupSize
$Ctrl = $Shuffled | Select-Object -Skip $GroupSize | Select-Object -First $GroupSize

$Exp | ForEach-Object { $_ | Add-Member -NotePropertyName "Group" -NotePropertyValue "Experimental" -Force }
$Ctrl | ForEach-Object { $_ | Add-Member -NotePropertyName "Group" -NotePropertyValue "Control" -Force }

$Result = $Exp + $Ctrl
$Result | Export-Csv $OutputFile -NoTypeInformation -Encoding UTF8

Write-Output "分组完成: 实验组 $($Exp.Count) 人, 对照组 $($Ctrl.Count) 人"
Write-Output "结果保存至: $OutputFile"
