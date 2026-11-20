# 110 OBSERVER

[English](#english) · [Русский](#russian) · [简体中文](#chinese)

| Edition / Издание / 版本 | PDF | LaTeX |
|---|---|---|
| English | [Observability of a System’s Own Past](./110_OBSERVER_Preprint_en.pdf) | [Source](./translations/en/main.tex) |
| Русский | [Наблюдаемость собственного прошлого](./110_OBSERVER_Preprint.pdf) | [Исходный текст](./main.tex) |
| 简体中文 | [系统自身过去的可观测性](./110_OBSERVER_Preprint_zh.pdf) | [源文件](./translations/zh/main.tex) |

<a id="english"></a>

## English

How many bits about its past does a system need for its next decision, and how can we tell whether it used them? T1–T4 give the decoding criterion and the cost of the message. In Rule 110, after two lattice configurations merge, an observer returns a sensor reading held in an external one-bit register. In frozen OLMo, the sender selects a rule token before seeing the new input. A recipient with a fresh KV cache uses that token. T5–T6 delimit the inference about subjective experience. [Full English preprint](./110_OBSERVER_Preprint_en.pdf)

**Evidence as of 20 November 2026.** Lean 4.35.0 checked all 263 modules of the lattice proof and all 11 axiom reports for the observer module. On the OLMo development panel, transmitting the rule gave 64/64 correct answers on strings with unequal end bits, compared with 32/64 for a constant A token. Across the full panel, the result was 124/128 answers and 6/8 complete blocks. The held-out panels have status `NOT_RUN`. [Geometry log](./verification/monograph/geometry-axioms.log) · [Observer log](./verification/monograph/observer-axioms.log) · [OLMo report](./observer/two-step-instruct-chat-04/report.json)

[Download the release and checksums](https://github.com/Dnarts/rule110-dependency-fronts/releases/tag/v2.2.1-monograph-multilingual) · [Verification commands](#verify) · [Citation](./CITATION.cff) · [Earlier editions](./archive/README.md)

<a id="russian"></a>

## Русский

Сколько битов о прошлом нужно системе для следующего решения и как проверить, что она ими воспользовалась? T1–T4 задают критерий декодирования и цену сообщения. В Rule 110 после слияния двух конфигураций решётки наблюдатель возвращает показание датчика из внешнего однобитного регистра. В замороженной OLMo отправитель выбирает токен правила до предъявления новой строки. Получатель применяет его со свежим KV-кэшем. T5–T6 устанавливают границы вывода о субъективном опыте. [Полный русский препринт](./110_OBSERVER_Preprint.pdf)

**Срез на 20 ноября 2026 г.** Lean 4.35.0 проверил 263 модуля доказательства о решётке и все 11 отчётов об аксиомах модуля наблюдателя. На строках dev-панели OLMo с разными концами передача правила дала 64/64 правильных ответа, постоянный токен A — 32/64. По всей панели получено 124/128 ответов и 6/8 полностью решённых блоков. Отложенные панели имеют статус `NOT_RUN`. [Журнал геометрии](./verification/monograph/geometry-axioms.log) · [Журнал наблюдателя](./verification/monograph/observer-axioms.log) · [Отчёт OLMo](./observer/two-step-instruct-chat-04/report.json)

[Скачать выпуск и контрольные суммы](https://github.com/Dnarts/rule110-dependency-fronts/releases/tag/v2.2.1-monograph-multilingual) · [Команды проверки](#verify) · [Для цитирования](./CITATION.cff) · [Предыдущие издания](./archive/README.md) · [Карта источников](./docs/series.md)

<a id="chinese"></a>

## 简体中文

系统为作出下一次决策，需要多少关于过去的信息？怎样检验它是否使用了这些信息？T1–T4 给出解码判据和消息代价。在规则 110 中，两个格点构型合并后，观察者把存放在外部单比特寄存器中的传感器读数送回格点。在冻结的 OLMo 中，发送方在看到新串之前选定规则词元，接收方从空的 KV 缓存开始计算并应用该规则。T5–T6 界定了由此推断主观体验的范围。[中文全文](./110_OBSERVER_Preprint_zh.pdf)

**截至 2026 年 11 月 20 日的验证结果。** Lean 4.35.0 已检查格点证明的全部 263 个模块及观察者模块的全部 11 份公理报告。在 OLMo 开发集上，对于首尾比特不同的串，传递规则时答对 64/64 个条件，使用恒定词元 A 时答对 32/64 个。在整个开发集上，答对 124/128 个条件，完整通过 6/8 个区组。留出面板的状态为 `NOT_RUN`。[几何证明日志](./verification/monograph/geometry-axioms.log) · [观察者模块日志](./verification/monograph/observer-axioms.log) · [OLMo 实验报告](./observer/two-step-instruct-chat-04/report.json)

[下载本版文件及校验和](https://github.com/Dnarts/rule110-dependency-fronts/releases/tag/v2.2.1-monograph-multilingual) · [验证命令](#verify) · [引用格式](./CITATION.cff) · [历次版本](./archive/README.md)

<a id="verify"></a>

## Verification · Проверка · 验证

From the repository root · Из корня репозитория · 在仓库根目录运行：

~~~sh
python3 -B observer/verify.py
python3 -B observer/verify_part_iii.py
~~~

The commands check the finite witnesses and recompute counts from the stored dev reports. Команды проверяют конечные свидетели и пересчитывают показатели по сохранённым dev-отчётам. 这两条命令验证有限见证，并根据已保存的开发集报告重新统计结果。

| Task / Задача / 任务 | Command |
|---|---|
| Lean proof and observer checks / Проверка Lean и наблюдателя / 检查 Lean 证明与观察者 | `make verify-series` (Lean 4.35.0, Python 3.10+) |
| Russian PDF / Русский PDF / 俄文版 | `make monograph` |
| English and Chinese PDFs / Английский и китайский PDF / 英文版与中文版 | `make translations` |

LaTeX engine / Движок / 排版引擎: Tectonic or XeLaTeX with latexmk.
