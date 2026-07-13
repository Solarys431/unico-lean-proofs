<div align="right">🌐 <a href="README.md">English</a> · <b>Italiano</b></div>

# unico-lean-proofs

[![Verify proofs](https://github.com/Solarys431/unico-lean-proofs/actions/workflows/build.yml/badge.svg)](https://github.com/Solarys431/unico-lean-proofs/actions/workflows/build.yml)
[![Lean 4](https://img.shields.io/badge/Lean-v4.32.0--rc1-blue)](https://leanprover.github.io/)
[![mathlib](https://img.shields.io/badge/mathlib-fissata-blue)](https://github.com/leanprover-community/mathlib4)
[![Licenza: Apache 2.0](https://img.shields.io/badge/licenza-Apache%202.0-green)](LICENSE)

**Dimostrazioni Lean 4 verificate dalla macchina, prodotte dalla pipeline
autonoma di certificazione UNICO / NOUS** — selezione degli enunciati →
falsificazione numerica → ricerca della dimostrazione con più motori →
certificazione del kernel in locale → ri-verifica pubblica in CI.
A cura di [Solarys431](https://github.com/Solarys431).

Ogni file compila con Lean 4 e non contiene alcun `sorry`. Il livello di
fiducia è dichiarato file per file — **kernel puro** (nulla oltre gli assiomi
di mathlib) oppure **compilatore** (`native_decide`, che aggiunge la fiducia
in `Lean.ofReduceBool` e nel compilatore) — perché l'onestà sulla base fidata
conta più di una lista più lunga di spunte verdi.

---

## In evidenza — Il teorema delle trisettrici di Morley (Wiedijk n. 84)

*Una formalizzazione geometrica indipendente in Lean (12 luglio 2026) — si veda la nota di prior art qui sotto.*

> In ogni triangolo non degenere, i tre punti d'incontro delle trisettrici
> adiacenti degli angoli formano un triangolo equilatero. — F. Morley, 1899

```lean
theorem morley_classico (A B C P₁ P₂ P₃ : ℂ)
    (hnc : ¬ Collinear ℝ ({A, B, C} : Set ℂ))
    (h₁ : P₁ ∈ trisettore A B C ∩ trisettore B A C)
    (h₂ : P₂ ∈ trisettore B C A ∩ trisettore C B A)
    (h₃ : P₃ ∈ trisettore C A B ∩ trisettore A C B) :
    dist P₁ P₂ = dist P₂ P₃ ∧ dist P₂ P₃ = dist P₃ P₁
```

L'enunciato è autenticamente geometrico, nello stile del `MORLEY` di Harrison
in HOL Light: `trisettore` è una semiretta nel piano complesso, i punti di
Morley entrano come ipotesi di appartenenza alle intersezioni delle semirette,
e la conclusione riguarda distanze fra punti veri. Due risultati compagni
chiudono le scappatoie classiche:
[`morley_esistenza_classico`](UnicoProofs/Morley.lean) (ogni coppia di
trisettrici adiacenti si incontra in **esattamente un** punto, `∃!`) e
[`morley_non_degenere_classico`](UnicoProofs/Morley.lean) (i tre punti sono
**a due a due distinti**: un triangolo vero, mai collassato in un punto).

**Nota di prior art (13 luglio 2026).** Il teorema di Morley è il n. 84 della
[lista di Freek Wiedijk](https://www.cs.ru.nl/~freek/100/) ed era elencato fra
i [16 teoremi non ancora formalizzati in Lean](https://leanprover-community.github.io/100-missing.html)
al momento della pubblicazione — ma a un'ora dall'annuncio, Jeremy Chen sullo
Zulip di Lean ci ha gentilmente segnalato il [benchmark lean-eval](https://leanprover.github.io/lean-eval-leaderboard/problems/morley_theorem),
il cui `morley_theorem` geometrico era già stato risolto da diversi sistemi AI
fra il 10 giugno e l'11 luglio 2026. **Questa non è dunque la prima
formalizzazione geometrica del teorema di Morley in Lean**, e correggiamo
volentieri il primato annunciato. Resta una formalizzazione indipendente, con
un enunciato diverso (semirette orientate via `arg`/3 in ℂ) e con i compagni
`∃!` e di non-degenerazione che l'enunciato del benchmark non richiede. Altri
sistemi: HOL Light (Harrison), Isabelle (Puyobro), Rocq (Guilhot), Mizar
(Coghetto); identità trigonometriche parziali in
[lean-genius](https://github.com/rjwalters/lean-genius).

**Fiducia: kernel puro** — 0 `sorry`, 0 assiomi aggiuntivi, nessuna
valutazione affidata al compilatore. Tag
[`morley-2026-07-12`](https://github.com/Solarys431/unico-lean-proofs/releases/tag/morley-2026-07-12).

---

## Tutte le dimostrazioni

| File | Enunciato | Fiducia | Autore della dimostrazione |
|------|-----------|:-------:|----------------------------|
| [`Morley.lean`](UnicoProofs/Morley.lean) | **Teorema delle trisettrici di Morley** (Wiedijk n. 84) — enunciato geometrico, con i compagni `∃!` e di non-degenerazione; formalizzazione indipendente (si veda la nota di prior art: risolto in precedenza sul [benchmark lean-eval](https://leanprover.github.io/lean-eval-leaderboard/problems/morley_theorem)) | ✅ kernel puro | Claude (Anthropic) |
| [`Erdos1064K2.lean`](UnicoProofs/Erdos1064K2.lean) | **Problema di Erdős 1064, variante k2** — esistono infiniti `n` con `φ(n) < φ(n − φ(n))` (Grytczuk–Luca–Wójtowicz 2001; dimostrazione equivalente indipendente in [lean-genius](https://github.com/rjwalters/lean-genius), 8 luglio 2026 — si veda la nota di prior art nel file) | ✅ kernel puro | Aristotle (Harmonic AI) |
| [`Erdos1148Counterexample.lean`](UnicoProofs/Erdos1148Counterexample.lean) | **Problema di Erdős 1148** — `6563` non è rappresentabile come `x² + y² − z²` con `max(x², y², z²) ≤ 6563` (il più grande intero noto con questa proprietà) | ⚙️ compilatore | Claude (Anthropic) |

Ogni file porta nell'intestazione le proprie note di provenienza e di prior art.

## Verificare da sé

```bash
# richiede elan: https://leanprover-community.github.io/get_started.html
git clone https://github.com/Solarys431/unico-lean-proofs
cd unico-lean-proofs
lake exe cache get   # scarica mathlib precompilata
lake build           # il kernel controlla ogni dimostrazione — termina senza errori
```

Toolchain: `leanprover/lean4:v4.32.0-rc1` · mathlib fissata da
[`lake-manifest.json`](lake-manifest.json). Il
[workflow di CI](.github/workflows/build.yml) esegue esattamente questa
compilazione a ogni push: il badge in cima alla pagina è la verifica pubblica
e indipendente.

## Metodo

UNICO / NOUS è una pipeline autonoma di scoperta e certificazione matematica.
Gli enunciati candidati vengono selezionati, sottoposti dove possibile a
falsificazione numerica, poi affrontati da più motori (Claude, Codex,
Aristotle), con il calcolo simbolico esatto (sympy) a fornire i cofattori
certificati per le dimostrazioni in stile `linear_combination`. Nulla entra in
questo repository se il kernel di Lean non lo certifica in locale — e la CI lo
ri-certifica in pubblico.

## Dichiarazione sull'uso dell'IA

Tutte le dimostrazioni sono **generate da modelli linguistici** (Aristotle di
Harmonic, Codex di OpenAI, Claude di Anthropic), con note di provenienza file
per file, sotto direzione umana. Il kernel di Lean è l'unico arbitro della
correttezza: nulla viene pubblicato se non compila.

## Come citare

Si veda [`CITATION.cff`](CITATION.cff), oppure si citi direttamente il
repository indicando il tag pertinente (es. `morley-2026-07-12`).

## Licenza

[Apache 2.0](LICENSE).
