<a id="top"></a>

# Rule 110: Essential Inputs and Memory After Coalescence

**110 OBSERVER · Research continuation · Aleksandr Strand · 21 November 2026**

## Read the paper

**[English PDF](paper/rule110-continuation-en.pdf) · [Русский PDF](paper/rule110-continuation-ru.pdf) · [PDF בעברית](paper/rule110-continuation-he.pdf)**

**[English](#english) · [Русский](#russian) · [简体中文](#chinese) · [עברית](#hebrew)**

[Mathematical relationship to the earlier work](docs/relationship.md) · [Verification report](verification/REPORT.md) · [Lean sources](lean/) · [Finite checks](scripts/check_finite.py)

**Earlier work:** [Rule 110 dependency fronts and 110 OBSERVER](https://github.com/Dnarts/rule110-dependency-fronts) · [Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory)

**Verified publication:** Lean 4.35.0 · **79/79 requested axiom reports** · only `propext` and `Quot.sound` · independent finite checks passed. [Package roles and reproduction](MANIFEST.md) · [English LaTeX](paper/rule110-continuation-en.tex) · [Citation](CITATION.cff).

---

<a id="english"></a>

## English — What this work adds

A system can depend on every part of its input while preserving very little information about that input. It can also lose a distinction in its own state while an earlier observation preserves exactly what a later decision needs. This paper makes both situations precise in **Rule 110**, a cellular automaton whose cells contain only 0 or 1 and update by one fixed local rule.

The contribution is a set of explicit constructions and proofs: a complete small-ring example, a certificate that protects a periodic background against an arbitrary tail, a completed formal proof of a four-step merging threshold, and a register that carries information between repeated episodes. The point is to make the source, loss, preservation, and later use of a distinction independently checkable.

### Four results, in ordinary language

| Result | What is established | Why the distinction matters |
|---|---|---|
| **Seven relevant inputs, fifteen possible states** | On a ring of seven cells, exactly 15 complete states remain reachable from step 7 onward. Every one of the seven original bits can nevertheless affect a later observation of cell 0. | An input can matter without being recoverable from the output. The number of influential inputs is not the amount of information retained. |
| **A protected periodic background** | For either of two specified phases, a periodic background remains exact on a moving left half-line, for every possible continuation on the right. | Checking a few example disturbances is different from proving protection against every allowed disturbance. |
| **A completed proof of the four-step threshold** | Within the specified class of observations, full merging first permits exact recovery requiring both the saved sensor bit and the surviving context at step 4. | A working example gives an upper bound. A matching impossibility proof establishes that no earlier example in the same class can work. |
| **Memory carried across episodes** | One register keeps the parity of earlier sensor readings. Changing its initial bit changes every subsequent output under the same episode schedule. | A fixed update rule can still maintain a changing, causally effective memory state. |

#### 1. Compression does not measure which inputs can matter

The seven-cell ring starts with 128 possible input strings. From step 7 onward it can reach only 15 states: the all-zero fixed point and a cycle of length 14. A fixed-length code needs **4 bits** to identify one of these 15 reached states.

Nevertheless, all **7 original input positions** are essential for the observed output bit at every such time. “Essential” means that changing that input alone changes the output for at least one suitable input string. The witnessing string may differ between positions and times. It does **not** mean that the output reveals all seven original bits, or that the complete initial string can be reconstructed.

This gives a fully specified example separating **influence**, **retained information**, and **the size of an exact output code**.

#### 2. An arbitrary environment is covered by a finite certificate

The second result starts with one of two phases of a periodic Rule 110 background on the left and an arbitrary binary tail from position 4 onward. At even time $t=2j$, the chosen phase remains exact at every position $x<-j$. The two phases remain distinguishable somewhere in that protected half-line.

A finite automaton with 63 reachable states checks both possible values of each newly encountered boundary bit. Its 126 transition checks support an induction covering every allowed tail and arbitrarily late even times. The theorem does not claim that its boundary speed is optimal.

#### 3. What is new about the threshold proof

The earlier **110 OBSERVER** monograph already supplied the four histories and claimed the threshold of four steps. This continuation completes the formal connection between the lower-bound argument and those histories: one theorem establishes both impossibility before step 4 and existence at step 4 under the same conventions.

The restrictions are part of the result. Within each context, two initial histories differ in one designated bit. They must become identical on the **entire infinite line**. A single raw sensor reads the same cell at the same earlier time in all four histories. The context is read from a fixed cell of the merged state, and neither context nor sensor reading alone may suffice for decoding.

Under these conditions, merging first occurs at **step 4**; writing back the saved bit lets the Rule 110 update return the original bit at **step 5**. The result is not a universal four-step bound for arbitrary sensors or memory systems.

#### 4. What the persistent register actually stores

For an episode with context $K_n$, original bit $Y_n$, and sensor reading $Z_n$, the construction gives $Z_n=K_n\oplus Y_n$. The register updates by

$$q_{n+1}=q_n\oplus Z_n,\qquad O_n=q_{n+1}\oplus K_n=q_n\oplus Y_n.$$

Thus the register stores a one-bit summary: the initial register value combined with the parity of previous readings. It does not store the full history, and the output need not equal the current original bit once earlier episodes have changed the register.

The **external schedule resets the lattice for each episode**. The register persists across these resets. This is an explicit model of persistent external memory, with its reset mechanism included in the description.

### How it connects to the two earlier projects

The [dependency-front work](https://github.com/Dnarts/rule110-dependency-fronts) asks which initial positions can affect an observation and how finite certificates establish statements for unbounded time. This continuation adds the exact seven-cell ring, the arbitrary-tail phase certificate, and a completed formal threshold theorem to that line of work.

[Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory) distinguishes an encoding channel, information useful for a task, and a joint update rule that carries memory through time. The four histories and the parity register provide concrete Rule 110 examples of these distinctions.

There is also a precise channel connection. In context 0 the sensor copies the original bit; in context 1 it inverts it. These are the identity and NOT binary channels. If the four histories are assigned equal probabilities, each of the two observations alone reveals no information about $Y$, but together they recover it:

$$I(Y;K)=I(Y;Z)=0,\qquad I(Y;Z\mid K)=1\text{ bit}.$$

The probability assignment is an additional choice for this interpretation. The paper's exact decoding statement itself does not require probabilities. The topology of continuously varying channels does not directly constrain a discrete context switch. The full mapping and its assumptions are set out in [the relationship note](docs/relationship.md).

### Where these results may help

These are **possible uses of the mathematical distinctions**, not experiments on deployed AI, robots, or physical sensors.

| Domain | A question this work helps formulate |
|---|---|
| Formal verification and cellular automata | Can a finite certificate cover every allowed boundary input and all later times? |
| AI and software with memory | Which state survives between episodes, how is it updated, and does it change later outputs under a controlled comparison? |
| Sensors and control | What must be measured before two histories become indistinguishable, and what context will decoding need later? |
| Compression and contextual coding | Are we preserving the full state, a task-relevant distinction, or merely a variable that can sometimes influence an output? |

The value is the ability to check these questions against explicit states, witnesses, and proofs. Extending the constructions to a different model requires checking that model's assumptions.

<details>
<summary>Sources, reproducibility, and proof scope</summary>

- Read the [English paper](paper/rule110-continuation-en.pdf) or the [original Russian paper](paper/rule110-continuation-ru.pdf).
- The [Lean directory](lean/) contains the formal sources, including the module connecting the threshold lower bound with its four-step witness.
- [verify_lean.py](scripts/verify_lean.py) checks the formal sources and axiom reports; [check_finite.py](scripts/check_finite.py) independently recomputes the finite tables.
- The [verification report](verification/REPORT.md) records the publication's actual check results and limitations. Finite enumeration and an induction proof have different roles; a finite table alone does not prove an unbounded-time claim.
- The [relationship note](docs/relationship.md) distinguishes results already present in the earlier work, formal completion, and additional deductions linking the projects. It does not claim that every information-theoretic bridge is formalized in Lean.
- [Supplied originals](archive/supplied/) preserve the incoming materials separately from the publication files.

</details>

[↑ Language menu](#top)

---

<a id="russian"></a>

## Русский — Что добавляет эта работа

Система может зависеть от каждой части входа, сохраняя при этом совсем немного сведений об этом входе. Она также может утратить различие в собственном состоянии, тогда как более раннее наблюдение сохранит именно то, что понадобится для последующего решения. В статье обе ситуации точно описаны на примере **правила 110** — клеточного автомата, в котором каждая клетка содержит 0 или 1 и обновляется по одному фиксированному локальному правилу.

Вклад работы — явные конструкции и доказательства: полностью разобранное небольшое кольцо, сертификат защиты периодического фона от произвольного хвоста, завершённое формальное доказательство четырёхтактного порога слияния и регистр, переносящий информацию между повторными эпизодами. Это позволяет отдельно проверить происхождение различия, его утрату, сохранение и последующее использование.

### Четыре результата простым языком

| Результат | Что установлено | Почему это различие важно |
|---|---|---|
| **Семь существенных входов, пятнадцать возможных состояний** | На кольце из семи клеток начиная с такта 7 достижимы ровно 15 полных состояний. При этом каждый из семи исходных битов может влиять на более позднее наблюдение клетки 0. | Вход может влиять на ответ, хотя восстановить его по ответу нельзя. Число существенных входов не равно количеству сохранённой информации. |
| **Защищённый периодический фон** | Для каждой из двух заданных фаз периодический фон точно сохраняется на движущейся левой полупрямой при любом продолжении справа. | Проверить несколько возмущений и доказать защиту от каждого допустимого возмущения — разные задачи. |
| **Завершённое доказательство порога в четыре такта** | В заданном классе наблюдений полное слияние впервые совместимо с точным восстановлением, требующим и сохранённого показания датчика, и оставшегося контекста, на такте 4. | Рабочий пример даёт верхнюю границу. Доказательство невозможности более раннего примера в том же классе делает границу точной. |
| **Память между эпизодами** | Один регистр хранит чётность прежних показаний. Изменение его начального бита меняет каждый следующий выход при том же расписании эпизодов. | Фиксированное правило обновления может поддерживать меняющееся состояние памяти, которое влияет на дальнейший результат. |

#### 1. Сжатие не измеряет, какие входы могут повлиять на ответ

У семиклеточного кольца 128 возможных начальных строк. Начиная с такта 7 оно может попасть лишь в 15 состояний: неподвижный ноль и цикл длины 14. Чтобы обозначить одно из этих достигнутых состояний кодом фиксированной длины, нужны **4 бита**.

При этом на каждом таком такте для наблюдаемого выходного бита существенны все **7 исходных позиций**. «Существенна» означает: существует подходящая исходная строка, в которой изменение только этой позиции меняет ответ. Для разных позиций и моментов времени строки-свидетели могут различаться. Это **не** означает, что выход сообщает все семь исходных битов или позволяет восстановить всю начальную строку.

Получается полностью заданный пример, разделяющий **влияние**, **сохранённую информацию** и **размер точного кода выхода**.

#### 2. Произвольное окружение покрывается конечным сертификатом

Второй результат задаёт слева одну из двух фаз периодического фона правила 110, а с позиции 4 разрешает произвольный двоичный хвост. В каждый чётный момент $t=2j$ выбранная фаза точно сохраняется во всех позициях $x<-j$. Где-то на этой защищённой полупрямой две фазы остаются различимыми.

Конечный автомат с 63 достижимыми состояниями проверяет оба значения каждого нового граничного бита. Его 126 проверок переходов поддерживают индукцию для любого допустимого хвоста и сколь угодно поздних чётных моментов. Оптимальность скорости границы здесь не утверждается.

#### 3. Что нового в доказательстве порога

В прежней монографии **110 OBSERVER** уже были четыре истории и утверждение о пороге в четыре такта. Это продолжение завершает формальную связь между нижней границей и этими историями: одна теорема устанавливает невозможность до такта 4 и существование на такте 4 при согласованных определениях.

Ограничения входят в сам результат. Внутри каждого контекста две начальные истории различаются одним выделенным битом. Они должны стать одинаковыми на **всей бесконечной прямой**. Один датчик снимает сырое показание в одной клетке и в один более ранний момент во всех четырёх историях. Контекст читается из фиксированной клетки слившегося состояния. Ни контекста, ни показания по отдельности не должно хватать для декодирования.

При этих условиях слияние впервые возможно на **такте 4**; запись сохранённого бита позволяет следующему обновлению правила 110 вернуть исходный бит на **такте 5**. Это не универсальная четырёхтактная граница для любых датчиков и систем памяти.

#### 4. Что на самом деле хранит постоянный регистр

Для эпизода с контекстом $K_n$, исходным битом $Y_n$ и показанием датчика $Z_n$ конструкция даёт $Z_n=K_n\oplus Y_n$. Регистр обновляется так:

$$q_{n+1}=q_n\oplus Z_n,\qquad O_n=q_{n+1}\oplus K_n=q_n\oplus Y_n.$$

Таким образом, регистр хранит однобитную сводку: своё начальное значение, сложенное по модулю два с чётностью прежних показаний. Он не хранит всю историю. После изменения регистра предыдущими эпизодами выход не обязательно равен текущему исходному биту.

**Внешнее расписание заново задаёт решётку для каждого эпизода**. Регистр сохраняется между этими перезапусками. Это явная модель постоянной внешней памяти, в описание которой включён механизм перезапуска.

### Как работа связана с двумя предыдущими проектами

Работа о [фронтах зависимости](https://github.com/Dnarts/rule110-dependency-fronts) выясняет, какие начальные позиции могут влиять на наблюдение и как конечные сертификаты доказывают утверждения для неограниченного времени. Это продолжение добавляет точный разбор семиклеточного кольца, сертификат сохранения фазы при произвольном хвосте и завершённую формальную теорему о пороге.

[Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory) различает канал кодирования, полезную для задачи информацию и совместное правило обновления, переносящее память во времени. Четыре истории и регистр чётности дают конкретные примеры этих различий в правиле 110.

Есть и точная связь через каналы. В контексте 0 датчик копирует исходный бит, а в контексте 1 инвертирует его. Это двоичные каналы тождества и NOT. Если назначить четырём историям одинаковые вероятности, каждое наблюдение отдельно не сообщает информации о $Y$, но вместе они восстанавливают его:

$$I(Y;K)=I(Y;Z)=0,\qquad I(Y;Z\mid K)=1\text{ бит}.$$

Распределение вероятностей — дополнительный выбор для этой интерпретации. Само точное декодирование в статье вероятностей не требует. Топология непрерывно меняющихся каналов непосредственно не ограничивает дискретное переключение контекста. Полное сопоставление и его предпосылки приведены в [заметке о связи работ](docs/relationship.md).

### Где результаты могут пригодиться

Это **возможные применения математических различий**, а не эксперименты на действующих ИИ, роботах или физических датчиках.

| Область | Какой вопрос помогает поставить работа |
|---|---|
| Формальная верификация и клеточные автоматы | Может ли конечный сертификат охватить все допустимые граничные входы и все последующие моменты? |
| ИИ и программы с памятью | Какое состояние переживает эпизоды, как обновляется и меняет ли поздние выходы при контролируемом сравнении? |
| Датчики и управление | Что нужно измерить до того, как истории станут неразличимыми, и какой контекст понадобится при декодировании? |
| Сжатие и контекстное кодирование | Что сохраняется: полное состояние, нужное для задачи различие или переменная, которая лишь иногда способна повлиять на выход? |

Ценность — в возможности проверить эти вопросы на явных состояниях, свидетелях и доказательствах. Перенос конструкций в другую модель требует проверки её предпосылок.

<details>
<summary>Источники, воспроизведение и границы доказательств</summary>

- Статья доступна [на английском](paper/rule110-continuation-en.pdf) и [в русском оригинале](paper/rule110-continuation-ru.pdf).
- В [каталоге Lean](lean/) находятся формальные исходники, включая модуль, соединяющий нижнюю границу порога с четырёхтактным свидетелем.
- [verify_lean.py](scripts/verify_lean.py) проверяет формальные исходники и отчёты об аксиомах; [check_finite.py](scripts/check_finite.py) независимо пересчитывает конечные таблицы.
- [Отчёт о проверке](verification/REPORT.md) фиксирует фактические результаты проверки публикации и ограничения. Конечный перебор и индукция выполняют разные задачи: сама по себе конечная таблица не доказывает утверждение для неограниченного времени.
- [Заметка о связи работ](docs/relationship.md) разделяет прежние результаты, завершение формализации и дополнительные выводы между проектами. Она не объявляет все информационные связи формализованными в Lean.
- [Переданные оригиналы](archive/supplied/) сохранены отдельно от файлов публикации.

</details>

[↑ Выбор языка](#top)

---

<a id="chinese"></a>

## 简体中文 — 这项工作增加了什么

一个系统的输出可能受到每个输入部分的影响，却只保留很少的输入信息。系统自身的状态也可能丢失某个区别，而先前的一次观测恰好保存了后续决策所需的信息。本文在 **110 号规则（Rule 110）** 中精确刻画这两种情况。这个元胞自动机的每个元胞只有 0 或 1，并按照同一个固定的局部规则更新。

本文的贡献是一组明确的构造与证明：完整分析一个小环、用证书保证周期背景不受任意右侧尾部影响、完成四步合并阈值的形式化证明，以及构造在重复回合之间传递信息的寄存器。这样就能分别核查一个区别从何而来、如何丢失、如何保留，以及以后如何被使用。

### 用普通语言说明四个结果

| 结果 | 已经建立的结论 | 为什么这一差别重要 |
|---|---|---|
| **七个本质输入，十五个可能状态** | 在七元胞环上，从第 7 步起，恰好有 15 个完整状态可达。然而，七个初始比特中的每一个仍然可能影响之后对元胞 0 的观测。 | 一个输入能够影响答案，并不意味着可以从答案中恢复它。本质输入的数量不等于保留的信息量。 |
| **受保护的周期背景** | 对指定的两种相位中的每一种，无论右侧如何延续，周期背景都在向左移动的半直线上保持精确。 | 检查几个扰动样例，与证明对所有允许的扰动都成立，是不同的任务。 |
| **完成四步阈值的证明** | 在指定的观测类别中，完整合并首次能够与精确恢复同时成立的时刻是第 4 步；恢复必须同时使用保存的传感器比特和仍然存在的上下文。 | 一个成功实例给出上界。证明同一类别中的更早实例不可能存在，才能得到精确阈值。 |
| **跨回合的记忆** | 一个寄存器保存此前读数的奇偶性。在相同回合安排下，改变寄存器的初始比特会改变每一个后续输出。 | 固定的更新规则仍然可以维护不断变化、并且实际影响后续结果的记忆状态。 |

#### 1. 压缩量不能说明哪些输入可能产生影响

七元胞环有 128 种可能的初始串。从第 7 步起，只能到达 15 个状态：全零不动点，以及一个长度为 14 的循环。用定长编码标识这 15 个到达状态中的一个，需要 **4 比特**。

但是，在此后的每个时刻，全部 **7 个初始位置**对被观测的输出比特都是本质的。“本质”是指：至少存在一个合适的初始串，只改变该位置就会改变输出。不同位置、不同时间可以使用不同的见证串。这**不**意味着输出揭示了全部七个初始比特，也不意味着能重建完整的初始串。

这是一个完全明确的例子，区分了**影响力**、**保留的信息**与**精确输出编码的长度**。

#### 2. 用有限证书覆盖任意环境

第二个结果在左侧放置 110 号规则周期背景的两个指定相位之一，并允许从位置 4 开始的二进制尾部完全任意。在每个偶数时刻 $t=2j$，所选相位在所有 $x<-j$ 的位置上都精确保持。在这条受保护的半直线上，两种相位始终能够在某个位置被区分。

一个具有 63 个可达状态的有限自动机，检查每个新遇到的边界比特的两种取值。这 126 次转移检查支持一个归纳证明，覆盖所有允许的尾部以及任意晚的偶数时刻。定理没有宣称边界移动速度是最优的。

#### 3. 阈值证明的新内容是什么

此前的 **110 OBSERVER** 专著已经给出了四条历史，并提出四步阈值。本篇续作完成了下界论证与这些历史之间的形式化连接：在统一的定义下，一条定理同时建立第 4 步之前的不可能性，以及第 4 步的可实现性。

限制条件本身就是结论的一部分。在每个上下文中，两条初始历史只在一个指定比特处不同；之后必须在**整条无限直线**上变得完全相同。单个原始传感器在全部四条历史中，于同一较早时刻读取同一个元胞。上下文从合并状态中的一个固定元胞读取，而且上下文或传感器读数中的任何一个单独都不能完成解码。

在这些条件下，首次合并发生于**第 4 步**；把保存的比特写回后，下一次 110 号规则更新在**第 5 步**返回原始比特。这不是针对任意传感器或记忆系统的普遍四步界限。

#### 4. 持续寄存器究竟保存什么

对于上下文为 $K_n$、原始比特为 $Y_n$、传感器读数为 $Z_n$ 的回合，构造满足 $Z_n=K_n\oplus Y_n$。寄存器按以下规则更新：

$$q_{n+1}=q_n\oplus Z_n,\qquad O_n=q_{n+1}\oplus K_n=q_n\oplus Y_n.$$

因此，寄存器保存的是一比特摘要：初始寄存器值与此前读数奇偶性的异或。它不保存完整历史。当前面的回合已经改变寄存器后，输出也不一定等于当前回合的原始比特。

**外部安排会在每个回合重新设置格点状态**。寄存器在这些重置之间保留。这是一个明确描述了重置机制的持续外部记忆模型。

### 与此前两个项目的关系

[依赖前沿研究](https://github.com/Dnarts/rule110-dependency-fronts)探讨哪些初始位置能够影响观测，以及如何用有限证书证明对无限时间范围成立的结论。本篇续作沿着这条路线增加了七元胞环的精确分析、任意尾部下的相位证书，以及完成形式化的阈值定理。

[Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory) 区分编码信道、对具体任务有用的信息，以及在时间中传递记忆的联合更新规则。四条历史和奇偶寄存器为这些区别提供了具体的 110 号规则实例。

还存在精确的信道联系：上下文为 0 时，传感器复制原始比特；上下文为 1 时，它将原始比特取反。两者分别是二元恒等信道与 NOT 信道。如果给四条历史赋予相同概率，两种观测单独都不提供关于 $Y$ 的信息，但合在一起可以恢复它：

$$I(Y;K)=I(Y;Z)=0,\qquad I(Y;Z\mid K)=1\text{ bit}.$$

这一概率分配是解释时额外作出的选择。论文本身的精确解码结论不需要概率。连续变化信道的拓扑并不直接限制离散的上下文切换。完整对应关系及其假设见[项目关系说明](docs/relationship.md)。

### 这些结果可能用在哪里

下面列出的是**这些数学区别的潜在用途**，并不是对已部署 AI、机器人或物理传感器进行的实验。

| 领域 | 本工作帮助明确的问题 |
|---|---|
| 形式化验证与元胞自动机 | 一个有限证书能否覆盖全部允许的边界输入与所有后续时刻？ |
| 带记忆的 AI 与软件 | 什么状态在回合之间保留、如何更新，以及它是否在受控比较中改变后续输出？ |
| 传感器与控制 | 在两条历史变得不可区分之前，必须测量什么？之后解码需要什么上下文？ |
| 压缩与上下文编码 | 保存的是完整状态、任务所需的区别，还是一个仅在某些情况下影响输出的变量？ |

其价值在于，可以针对明确的状态、见证和证明来检查这些问题。将构造推广到其他模型，需要核查该模型的假设。

<details>
<summary>来源、复现与证明范围</summary>

- 阅读[英文论文](paper/rule110-continuation-en.pdf)或[俄文原稿](paper/rule110-continuation-ru.pdf)。
- [Lean 目录](lean/)包含形式化源代码，以及将阈值下界与四步见证连接起来的模块。
- [verify_lean.py](scripts/verify_lean.py) 检查形式化源代码和公理报告；[check_finite.py](scripts/check_finite.py) 独立重新计算有限表格。
- [验证报告](verification/REPORT.md)记录本次发布实际完成的检查及其局限。有限枚举与归纳证明承担不同的作用；单独一张有限表格不能证明无限时间结论。
- [项目关系说明](docs/relationship.md)区分此前已有的结果、形式化的完成，以及连接各项目的额外推导。它没有宣称所有信息论联系都已在 Lean 中形式化。
- [提供的原始材料](archive/supplied/)与发布文件分开保留。

</details>

[↑ 语言菜单](#top)

---

<a id="hebrew"></a>

<div dir="rtl" align="right">

## עברית — מה העבודה מוסיפה

מערכת יכולה להיות תלויה בכל חלק של הקלט שלה, ובה בעת לשמר מעט מאוד מידע על הקלט. היא יכולה גם לאבד הבחנה במצבה הפנימי, בעוד שתצפית מוקדמת שומרת בדיוק את מה שיידרש להחלטה מאוחרת יותר. המאמר מנסח את שני המצבים במדויק באמצעות **כלל 110**: אוטומט תאי שבו כל תא מכיל 0 או 1 ומתעדכן לפי אותו כלל מקומי קבוע.

התרומה היא סדרת בניות והוכחות מפורשות: דוגמה מלאה של טבעת קטנה, תעודה המגינה על רקע מחזורי מפני המשך ימני שרירותי, השלמת הוכחה פורמלית לסף התמזגות של ארבעה צעדים, ואוגר שמעביר מידע בין אפיזודות חוזרות. כך אפשר לבדוק בנפרד מה מקור ההבחנה, כיצד היא אובדת, כיצד היא נשמרת וכיצד משתמשים בה בהמשך.

### ארבע תוצאות בשפה פשוטה

| תוצאה | מה הוכח | מדוע ההבחנה חשובה |
|---|---|---|
| **שבעה קלטים חיוניים, חמישה־עשר מצבים אפשריים** | בטבעת של שבעה תאים, החל מצעד 7 נגישים בדיוק 15 מצבים מלאים. ובכל זאת, כל אחד משבעת הביטים ההתחלתיים עשוי להשפיע על תצפית מאוחרת בתא 0. | קלט יכול להשפיע על תשובה בלי שאפשר יהיה לשחזר אותו ממנה. מספר הקלטים המשפיעים אינו כמות המידע שנשמר. |
| **רקע מחזורי מוגן** | בכל אחת משתי פאזות מוגדרות, הרקע המחזורי נשמר בדיוק על חצי ישר שמאלי נע, לכל המשך אפשרי מצד ימין. | בדיקת כמה הפרעות לדוגמה שונה מהוכחה המכסה כל הפרעה מותרת. |
| **השלמת הוכחת הסף של ארבעה צעדים** | במחלקת התצפיות שהוגדרה, התמזגות מלאה מאפשרת לראשונה שחזור מדויק המחייב גם את ביט החיישן שנשמר וגם את ההקשר שנותר, בצעד 4. | דוגמה שעובדת נותנת חסם עליון. הוכחת אי־אפשרות לדוגמה מוקדמת יותר באותה מחלקה הופכת את החסם למדויק. |
| **זיכרון בין אפיזודות** | אוגר יחיד שומר את הזוגיות של קריאות קודמות. שינוי הביט ההתחלתי שלו משנה כל פלט בהמשך תחת אותו סדר אפיזודות. | כלל עדכון קבוע יכול לשמר מצב זיכרון משתנה שמשפיע בפועל על תוצאות מאוחרות. |

#### 1. מידת הדחיסה אינה מודדת אילו קלטים יכולים להשפיע

לטבעת בת שבעה תאים יש 128 מחרוזות התחלתיות אפשריות. החל מצעד 7 אפשר להגיע רק ל־15 מצבים: מצב האפס הקבוע ומחזור באורך 14. קוד באורך קבוע צריך **4 ביטים** כדי לזהות אחד מ־15 המצבים שהתקבלו.

ובכל זאת, בכל זמן כזה כל **7 מיקומי הקלט המקוריים** חיוניים לביט הפלט הנצפה. ״חיוני״ פירושו שקיימת לפחות מחרוזת התחלתית מתאימה אחת שבה שינוי המיקום הזה בלבד משנה את הפלט. מחרוזת העדות יכולה להיות שונה למיקומים ולזמנים שונים. אין פירוש הדבר שהפלט מגלה את כל שבעת הביטים המקוריים, או שאפשר לשחזר ממנו את המחרוזת ההתחלתית כולה.

זו דוגמה מוגדרת במלואה המפרידה בין **השפעה**, **מידע שנשמר** ו**אורך קוד מדויק לפלט**.

#### 2. תעודה סופית מכסה סביבה שרירותית

התוצאה השנייה מתחילה באחת משתי פאזות של רקע מחזורי של כלל 110 בצד שמאל, ומאפשרת זנב בינרי שרירותי החל ממיקום 4. בכל זמן זוגי $t=2j$, הפאזה שנבחרה נשמרת בדיוק בכל מיקום $x<-j$. בכל זמן כזה אפשר להבחין בין שתי הפאזות במקום כלשהו בחצי הישר המוגן.

אוטומט סופי בעל 63 מצבים נגישים בודק את שני הערכים האפשריים של כל ביט גבול חדש. 126 בדיקות המעבר שלו תומכות באינדוקציה המכסה כל זנב מותר וכל זמן זוגי מאוחר ככל שיהיה. המשפט אינו טוען שמהירות הגבול היא מיטבית.

#### 3. מה חדש בהוכחת הסף

המונוגרפיה הקודמת **110 OBSERVER** כבר הציגה את ארבע ההיסטוריות וטענה לסף של ארבעה צעדים. ההמשך הזה משלים את הקישור הפורמלי בין טיעון החסם התחתון לבין ההיסטוריות האלה: משפט אחד קובע גם אי־אפשרות לפני צעד 4 וגם קיום בצעד 4, תחת הגדרות תואמות.

המגבלות הן חלק מהתוצאה. בכל הקשר, שתי היסטוריות התחלתיות נבדלות בביט מסוים אחד. עליהן להפוך לזהות על **הישר האינסופי כולו**. חיישן יחיד קורא ביט גולמי מאותו תא ובאותו זמן מוקדם בכל ארבע ההיסטוריות. ההקשר נקרא מתא קבוע במצב שהתמזג, ולא ההקשר לבדו ולא קריאת החיישן לבדה רשאים להספיק לפענוח.

בתנאים האלה, התמזגות מתאפשרת לראשונה **בצעד 4**; כתיבת הביט שנשמר בחזרה מאפשרת לעדכון הבא של כלל 110 להחזיר את הביט המקורי **בצעד 5**. זה אינו חסם אוניברסלי של ארבעה צעדים לכל חיישן או מערכת זיכרון.

#### 4. מה האוגר המתמשך שומר בפועל

באפיזודה שבה ההקשר הוא $K_n$, הביט המקורי הוא $Y_n$ וקריאת החיישן היא $Z_n$, הבנייה נותנת $Z_n=K_n\oplus Y_n$. האוגר מתעדכן כך:

<div dir="ltr" align="center">

$$q_{n+1}=q_n\oplus Z_n,\qquad O_n=q_{n+1}\oplus K_n=q_n\oplus Y_n.$$

</div>

כלומר, האוגר שומר סיכום בן ביט אחד: ערכו ההתחלתי משולב ב־XOR עם זוגיות הקריאות הקודמות. הוא אינו שומר את ההיסטוריה המלאה, ולאחר שאפיזודות קודמות שינו אותו, הפלט אינו חייב להיות שווה לביט המקורי של האפיזודה הנוכחית.

**לוח אפיזודות חיצוני מגדיר את הסריג מחדש בכל אפיזודה**. האוגר נשמר בין האתחולים האלה. זהו מודל מפורש לזיכרון חיצוני מתמשך, שמנגנון האתחול שלו נכלל בתיאור.

### איך העבודה מתחברת לשני הפרויקטים הקודמים

העבודה על [חזיתות התלות](https://github.com/Dnarts/rule110-dependency-fronts) שואלת אילו מיקומים התחלתיים יכולים להשפיע על תצפית, וכיצד תעודות סופיות מוכיחות טענות לזמן בלתי מוגבל. ההמשך הזה מוסיף ניתוח מדויק של טבעת בת שבעה תאים, תעודת שימור פאזה מול זנב שרירותי ומשפט סף שהפורמליזציה שלו הושלמה.

[Channel Topology and Memory](https://github.com/Dnarts/channel-topology-and-memory) מבחין בין ערוץ קידוד, מידע שימושי למשימה וכלל עדכון משותף המעביר זיכרון בזמן. ארבע ההיסטוריות ואוגר הזוגיות נותנים דוגמאות מוחשיות להבחנות האלה בכלל 110.

יש גם קשר מדויק דרך ערוצים. בהקשר 0 החיישן מעתיק את הביט המקורי; בהקשר 1 הוא הופך אותו. אלה הערוץ הבינרי הזהותי וערוץ NOT. אם מקצים הסתברות שווה לארבע ההיסטוריות, כל תצפית בנפרד אינה מספקת מידע על $Y$, אך יחד הן משחזרות אותו:

<div dir="ltr" align="center">

$$I(Y;K)=I(Y;Z)=0,\qquad I(Y;Z\mid K)=1\text{ bit}.$$

</div>

הקצאת ההסתברויות היא בחירה נוספת לצורך הפרשנות הזאת. טענת הפענוח המדויק במאמר עצמו אינה דורשת הסתברויות. הטופולוגיה של ערוצים המשתנים ברציפות אינה מגבילה ישירות מעבר בדיד בין הקשרים. המיפוי המלא וההנחות שלו מופיעים ב[הערה על הקשר בין העבודות](docs/relationship.md).

### היכן התוצאות עשויות לעזור

אלה **שימושים אפשריים בהבחנות המתמטיות**, ולא ניסויים במערכות AI פעילות, ברובוטים או בחיישנים פיזיים.

| תחום | שאלה שהעבודה עוזרת לנסח |
|---|---|
| אימות פורמלי ואוטומטים תאיים | האם תעודה סופית יכולה לכסות את כל קלטי הגבול המותרים ואת כל הזמנים המאוחרים? |
| AI ותוכנה עם זיכרון | איזה מצב נשמר בין אפיזודות, כיצד הוא מתעדכן, והאם הוא משנה פלטים מאוחרים בהשוואה מבוקרת? |
| חיישנים ובקרה | מה צריך למדוד לפני ששתי היסטוריות נעשות בלתי ניתנות להבחנה, ואיזה הקשר יידרש לפענוח בהמשך? |
| דחיסה וקידוד תלוי הקשר | האם נשמר המצב המלא, ההבחנה הדרושה למשימה, או רק משתנה שיכול לפעמים להשפיע על הפלט? |

הערך הוא האפשרות לבדוק את השאלות האלה מול מצבים, עדים והוכחות מפורשים. העברת הבניות למודל אחר מחייבת לבדוק את הנחותיו.

<details>
<summary>מקורות, שחזור והיקף ההוכחות</summary>

- קראו את [המאמר המלא בעברית](paper/rule110-continuation-he.pdf), את [המאמר באנגלית](paper/rule110-continuation-en.pdf) או את [המקור הרוסי](paper/rule110-continuation-ru.pdf).
- [תיקיית Lean](lean/) כוללת את המקורות הפורמליים, ובהם המודול שמחבר את חסם הסף התחתון לעד בן ארבעת הצעדים.
- [verify_lean.py](scripts/verify_lean.py) בודק את המקורות הפורמליים ואת דוחות האקסיומות; [check_finite.py](scripts/check_finite.py) מחשב מחדש באופן עצמאי את הטבלאות הסופיות.
- [דוח האימות](verification/REPORT.md) מתעד את הבדיקות שבוצעו בפועל עבור הפרסום ואת מגבלותיהן. למנייה סופית ולהוכחת אינדוקציה יש תפקידים שונים; טבלה סופית לבדה אינה מוכיחה טענה לזמן בלתי מוגבל.
- [ההערה על הקשר בין העבודות](docs/relationship.md) מפרידה בין תוצאות קודמות, השלמת פורמליזציה ומסקנות נוספות המחברות בין הפרויקטים. היא אינה טוענת שכל הקשרים בתורת המידע עברו פורמליזציה ב־Lean.
- [המקורות שסופקו](archive/supplied/) נשמרים בנפרד מקובצי הפרסום.

</details>

[↑ תפריט השפות](#top)

</div>

---

**Licenses:** [MIT for code](../LICENSE-CODE) · [CC BY 4.0 for the manuscript](../LICENSE-PAPER.md). The author is Aleksandr Strand; text preparation, translation, and verification code received assistance from ChatGPT.
