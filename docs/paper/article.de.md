# Die Dualität des Vertrauens: ein formal verifiziertes, informationstheoretisches Axiomensystem für Vertrauen, geprüft gegen die Quantengravitation

*Entwurf für den Eigentümer, 27.10.2026. Einreichungsspezifikation: [README.md](README.md). Englische Fassung: [article.en.md](article.en.md).*

**Autor.** Steven Hrovat (Kontakt: siehe Einreichungsspezifikation; nie das private Postfach).

**Zusammenfassung.** Infrastruktur wird aus vielen Systemen zusammengesetzt, die jedes für sich über Vertrauen entscheiden; ein
kompromittierter Zeuge entscheidet damit für alle. Wir stellen DMP vor, das Dark Matter Protocol, ein Axiomensystem, in dem keine Handlung
geschieht, solange nicht zwei unabhängige Zeugen, einer für das Vertrauen und einer für die Information zuständig, sie auf selbst geprüfter
Evidenz durchlassen, und in dem jeder Eintrag für die Zeugen der Handlung lesbar ist und von allen anderen nur gezählt, nie gelesen wird.
Wir geben die drei Axiome, den Grund G0, der das erste Vertrauen außerhalb jeder Ableitung setzt, und den Begriff der DMP-vollständigen
Konfiguration. Dann stellen wir Gravity vor, die Verifikation von DMP: ein Modell in Lean 4 (nur Kernbibliothek), in dem jede Anordnung,
die ein System annehmen kann, ein Term eines einzigen abgeschlossenen induktiven Typs ist, des Rezepts, und in dem die Axiome und Sätze von
DMP für jeden Term durch Induktion über die Zeilen des Rezepts bewiesen sind. Die 232 Sätze werden vom Lean-Kern geprüft und von einem
unabhängig geschriebenen Kern nachgeprüft, ruhen auf nichts außer propositionaler Extensionalität, Quotientenkorrektheit und Auswahl und
umfassen das Tor als Infimum in einem Sicherheitsverband, zwei unabhängige Zeugen hinter jedem Durchlass, die Zurückweisung einer Wurzel,
die auf eine Partei zurückgeht, die Rahmenregel für das Wachsen einer Konfiguration, die Unabhängigkeit der Entscheidungen von der
Platzierung, den Fingerabdruck des erwarteten Feldes und ein sich selbst beweisendes Veröffentlichungsformat für eine Konfiguration samt
Kaltstart. Das Modell steht auf veröffentlichten Ergebnissen (fail-prone systems, Dennings Verband, die Rahmenregel, Noninterference,
Selbststabilisierung, Potentialspiele), und wir berichten, was die Beweise hervorbrachten, was der Text nicht gesagt hatte. Schließlich
prüfen wir das Axiomensystem Ebene für Ebene gegen die Quantengravitation: Es reproduziert die klassische Gestalt der Gravitation über
bekannte Sätze und scheitert, beweisbar, an genau einer Stelle, an der zwei isolierte Hälften verschränkt sein müssten. Die Repositorien
sind öffentlich unter Apache 2.0.

**Schlagwörter.** Vertrauen, formale Verifikation, Lean 4, byzantinische Quorumsysteme, Sicherheitsverband, Noninterference,
Selbststabilisierung, informationstheoretische Axiome, Quantengravitation.

## 1. Einleitung

Die Infrastruktur einer Organisation wird von vielen Systemen betrieben: einem Verzeichnisdienst, einem Mandanten, einem Maildienst, einer
Geräteverwaltung, einem Monitoring, einer Sicherung, einem Hypervisor, einer Wissensbasis, einem Coding-Agenten. Jedes entscheidet über
Vertrauen nach eigenen Regeln, und ein Verwaltungswerkzeug, das sie alle umspannt, erbt jede dieser Entscheidungen. Der praktische Fehler
ist immer derselbe: Ein Zeuge entscheidet für alle. Ein einzelnes Administratorkonto, ein einzelner Signaturschlüssel, eine einzelne
Freigabeliste, das Urteil eines einzelnen Agenten genügt, um eine Handlung durchzulassen, die sonst niemand gesehen hat.

DMP ist eine Antwort auf diesen Fehler, als Axiomensystem gefasst statt als Produkt. Sein Eigentümer hat die These in einen Satz gelegt:
„This is basically marriage of demand aware self-adjusted routing with GR's informational black hole, applied purposefully for their
advantages, while cancelling out the disadvantages of the other at the same time through DoT and interpreted for general Software
Alignment" (26.10.2026). Die Dualität des Vertrauens, DoT, ist der eine Begriff, der durch jede Schicht läuft: zwei unabhängige Zeugen,
einer für das Vertrauen und einer für die Information zuständig, jeder mit vollem Zugriff auf die Handlung und nur vom anderen begrenzt.

Gravity ist der Beweis, dass das Axiomensystem für jede Konfiguration gilt, die es zulässt. Seine Behauptung ist nicht, dass eine bestimmte
Installation sicher ist, sondern dass es im Möglichkeitsraum des Systems keine Anordnung gibt, in der ein Axiom oder ein Satz verletzt ist.
Das Mittel dafür ist ein abgeschlossener induktiver Typ, das Rezept: eine nummerierte Liste von Zeilen, von denen jede eine Schicht über
einer früheren Zeile hinzufügt. Ein Satz, der für jeden Term des Typs bewiesen ist, ist für jede Anordnung bewiesen, denn eine Anordnung,
die kein Term ist, existiert nicht.

Dieser Artikel leistet:

1. das Axiomensystem DMP in seiner gegenwärtigen Form (drei Axiome, der Grund G0, die Begriffe) samt dem Begriff der DMP-vollständigen
   Konfiguration (Abschnitt 2);
2. das Gravity-Modell von DMP in Lean 4 und seine vereinheitlichte Theorie: die strukturellen Sätze, die jede Zeile jedes Rezepts überleben
   (Abschnitt 3), die Befunde, die die Beweise zutage förderten (Abschnitt 4), und ein sich selbst beweisendes Veröffentlichungsformat für
   eine Konfiguration samt Kaltstart (Abschnitt 5);
3. die Verifikationsmethode: zwei unabhängige Ketten, zwei unabhängige Kerne, eine verankerte Wurzelkette, ein abgeschlossener
   Möglichkeitsraum (Abschnitt 6);
4. eine Darstellung der veröffentlichten Ergebnisse, auf denen das Modell ruht, mit dem, was jedem entnommen wurde (Abschnitt 7);
5. eine Prüfung des Axiomensystems Ebene für Ebene gegen die Quantengravitation, mit der einen Stelle, an der es scheitert (Abschnitt 8).

Alles, was in diesem Artikel als bewiesen bezeichnet wird, ist ein Satz im öffentlichen Repositorium, von zwei Kernen geprüft; alles, was
als Kandidat bezeichnet wird, ist so gekennzeichnet. Satznamen stehen in `Schreibmaschinenschrift`, damit der Leser sie findet.

## 2. Das Axiomensystem

DMP ist als Verfassung geschrieben: eine Seite Regeln, die sich nicht biegen, gefolgt von Kapiteln, die beschreiben, wie jeder Teil gebaut
wird. Wir geben den Kern der Verfassung, wie er in Version 0.9.8 steht; der volle Text liegt im Repositorium.

### 2.1 Die Begriffe

Undefiniert, wie Punkt und Gerade, sind ein **Teil** (eine Dualität des Vertrauens: zwei Hälften, eine für das Vertrauen und eine für die
Information zuständig; mehr wird über einen Teil nicht gesagt), eine **Handlung**, ein **Zeuge** (ein Teil, der für andere über Vertrauen
entscheidet), **Evidenz** (was ein Zeuge prüft) und **Zeit**. Vertrauen ist eine Relation `T(w, p, a, t)` zwischen Zeuge, Teil, Handlung
und Zeit. Ein **Stand** ist Vertrauen über die Zeit hinweg; **Handlungsvertrauen** ist Vertrauen für eine Handlung jetzt.

Zwei Zeugen sind **unabhängig**, wenn sie kein Mitglied der Fehlerklassen teilen, die für ihre Schicht im Prägungsprotokoll erklärt sind
(Host, Schlüssel, Autor, Engine, Betriebsabbild, Person, Zeitquelle und was die Prägung sonst aufführt); Unabhängigkeit ist immer relativ zu
dieser Liste. Eine **Schicht** ist ein Ort, an dem über Vertrauen entschieden wird; ihre zwei Zeugen sind ihre **Hälften**, die
**Vertrauenshälfte** (ob eine Handlung geschehen darf) und die **Informationshälfte** (ob die Handlung gemeint und richtig ist); das Paar an
einer Schicht ist die **Dualität des Vertrauens**. Ein **Eintrag** ist Evidenz, die die Handlung überdauert. Eine Grenze **hält Information
ein**, wenn kein Teil jenseits der Grenze für irgendeine Handlung an dieser Information vertraut ist, sodass keine Handlung sie hinüberträgt.

Eine Konfiguration ist **DMP-vollständig**, wenn sie das Axiomensystem vollständig und beweisbar einhält: die Begriffe, jedes Axiom und
jeder Satz gelten für sie ganz, und beide Beweisketten beweisen es. Die Konfiguration schließt das Repositorium ein, aus dem sie gebaut
wird, mit jeder Abhängigkeit per Hash darin verankert, sodass sie sich ohne Verbindung über ihre Grenze selbst heilen kann. Ein Teil, den
die Ketten nicht beide erreichen oder der etwas von außerhalb des Repositoriums braucht, zählt als unbewiesen, und eine Konfiguration mit
einem unbewiesenen Teil ist nicht DMP-vollständig.

### 2.2 Die drei Axiome

**Axiom 1, die Dualität.** Ein Teil handelt nur, solange die zwei Hälften seiner Schicht, zwei unabhängige Zeugen, jeder mit vollem
Zugriff auf die Handlung und nur vom anderen begrenzt, ihm für diese Handlung vertrauen. Eine Hälfte ist für das Vertrauen zuständig, die
andere für die Information; keine überstimmt die andere. Was nicht beide vertrauen, handelt nicht. Jede Eingabe erhält genau eine Antwort,
und das Tor hat keinen anderen Weg hindurch. Wo die beiden uneins sind, gilt die strengere Antwort. Das gilt auf jeder Schicht. Die Balance
ist die Richtung des Systems: Jeder Teil arbeitet auf das Vertrauen hin, das die Dualität für ihre Grenze erklärt hat, stellt durch Evidenz
wieder her, was ohne Evidenz dagegen verloren ging, und senkt dafür nie die Evidenzschwelle.

**Axiom 2, Vertrauen.** Ein Zeuge vertraut nur auf Evidenz, die er selbst am Ort des Gebrauchs geprüft hat: den Live-Zustand des Teils und
den aktuellen Stand des Eintrags. Nie die Prüfung eines Überbringers, ein früheres Lesen, eine Behauptung, eine Erinnerung oder eine
Position im Netz. Information wird nie vertraut: Was ein Teil sagt, trägt, speichert oder weiterleitet, ist nie Evidenz für sich selbst.
Das Fehlen von Evidenz bewegt nichts. Vertrauen ist gravitativ: ein Feld, nie eine Position, in dem jeder Stand eine Quelle, eine Tiefe und
eine zerfallende Frische hat; das Feld fügt Stufen der geforderten Beweislast hinzu, nie Stufen des Vertrauens, und eine Grenze, die stark
genug ist, hält ein, was kein Vertrauen erreicht, sodass nur Entropie sie noch verlässt.

**Axiom 3, Information.** Jede Gewährung, jeder Gebrauch und jeder Verlust von Vertrauen hinterlässt einen Eintrag, bei der Handlung
geschrieben, den jeder Zeuge der Handlung vollständig lesen kann und der die Handlung überdauert; jeder andere sieht stets die Zählung und
den Inhalt nur durch eine Gewährung. Aus Vertrauen lässt sich über Information nichts ableiten als ihre Existenz. Inhalt bewegt sich nur
durch eine Gewährung an einen für seine Klasse vertrauten Teil, und wo kein Vertrauen hinreicht, ist Information eingehalten. Information
ist hierarchisch: Jedes Stück sitzt in einer Schicht, jede Schicht hat ihre eigene Dualität und ist ein dort verwurzelter Baum, eine
Unterschicht verschärft nur, was die Schicht darüber erlaubt, und der Baum trägt kein Vertrauen. Information entwickelt sich: Ein System
ordnet sich auf die wenigsten Gesamtsprünge für die repräsentative Zusammensetzung seiner Anfragen hin, von beiden Hälften neu berechnet
und nie von einer.

### 2.3 Der Grund

Das doppelte Tor kann seine eigene erste Instanz nicht bezeugen: Jemand muss den ersten zwei Zeugen vertrauen. Diese Handlung ist die
**Prägung** (G0): Mindestens fünf Teile werden Halter der Wurzelschlüssel, und diese Prägung zieht die Grenze der Instanz. Bis sie
geschieht, stehen die Worte des Eigentümers für beide Hälften. Eine **gepresste** Instanz, deren zwei Zeugen auf einen Teil zurückgehen,
ist auf allem, was sie ausgibt, so markiert und wird von einer geprägten nie voll vertraut. Eine Prägung wird nur für eine beweisbar
DMP-vollständige Konfiguration versucht (Prägungsvorbereitung). Zwei Sätze schließen den Ring: Vertrauen und Information begrenzen
einander, sodass nur eine Dualität, die sowohl vertraut ist als auch die ihr zugelassene Information hält, Teil eines geprägten Systems ist
(T39); und eine Prägung geht nur aus G0 zusammen mit einem DMP-vollständigen Zustand hervor, aus keinem allein (T40). G0 enthält auch die
Klausel des Eigentümers zu einer echten allgemeinen künstlichen Intelligenz: Ein solcher Teil ist, wird er erkannt, Bestandteil der Prägung
und nie nur ein regierter Teil unter dem Grund.

### 2.4 Warum Axiome und nicht eine Spezifikation

Eine Spezifikation sagt, was ein System tut. DMP sagt, was jedes System, das den Namen beansprucht, auf jeder Schicht und unter jeder
Zusammensetzung einhalten muss. Darum muss es ein Axiomensystem mit Sätzen sein, und darum kann seine Verifikation keine Testsammlung sein:
Ein Test zeigt eine Anordnung, ein Satz über einen abgeschlossenen Typ zeigt alle. Die Verfassung gilt auch für sich selbst (T22) und für
die Werkzeuge, die sie prüfen: Der Prüfer, der eine Konfiguration gegen DMP prüft, ist selbst Teil der Konfiguration und in ihr per Hash
verankert.

## 3. Das Modell und die vereinheitlichte Theorie

Gravitys Evidenzkette ist eine Lean-4-Entwicklung, nur Kernbibliothek, kein Mathlib, im Namensraum `Dmp`. Sie ist aus den Sätzen einer
byteweise übernommenen Kopie von DMP geschrieben, per Commit und Hash verankert; die Prüfung, dass die Kopie ihrem Anker entspricht, läuft
vor allem anderen, denn ein Beweis aus Sätzen, die niemand verankert hat, beweist nichts. Wir beschreiben die Dateien, die die
vereinheitlichte Theorie tragen; die früheren Dateien modellieren das doppelte Tor, den Eintrag, den Grund, Stände, den Entropieboden, das
Vertrauensfeld und den Milky-Way-Prüfer.

### 3.1 Zeugen, Unabhängigkeit, die Dualität

Eine **Fehlerklasse** ist eine natürliche Zahl; die **Person** ist Klasse 0. Ein **Zeuge** ist eine Funktion von Klassen auf Mitglieder:
der Host, auf dem er läuft, der Schlüssel, mit dem er signiert, die Person, auf die er zurückgeht. Zwei Zeugen sind `independent fcl w1 w2`,
wenn sie sich in jeder erklärten Klasse unterscheiden. Das ist das fail-prone system von Malkhi und Reiter, gelesen für ein Quorum von
zwei: Eine fehleranfällige Menge ist „jeder Zeuge auf Host h", und Unabhängigkeit heißt „keine fehleranfällige Menge enthält beide"
(`independent_iff_no_shared_failProne`). Sie ist symmetrisch, und mehr erklärte Klassen können sie nur aufheben
(`independent_of_superlist`). Eine `DoT` ist zwei Zeugen und ist `minted`, wenn sie auf der Person und jeder erklärten Klasse unabhängig
sind. Die Person ist keine Konfiguration: Mit leerer Klassenliste wären je zwei Zeugen unabhängig, derselbe Zeuge zweimal eingeschlossen
(`empty_list_makes_everything_independent`), darum liest das Modell die Liste als `person :: fcl` (Befund F1).

Das Tor der Schicht, `DoT.gate`, lässt eine Handlung nur durch, wenn beide Hälften sie auf Live-Evidenz durchließen
(`DoT.gate_pass_needs_both`). Ein Einfluss, der auf eine fehleranfällige Menge beschränkt ist, lässt auf einem geprägten Paar nie allein
eine Handlung durch (`DoT.confined_influence_never_passes_alone`); ein ungeprägtes Paar kollabiert: Eine gemeinsame Ursache lässt jede
Handlung durch (`DoT.not_minted_collapses`).

### 3.2 Das Rezept

Eine **Zeile** ist eine Schicht einer Art (Galaxie, Informationsschicht, Privatsphären-Singularität, Zwerggalaxie, Oberfläche), ihre
Dualität, die Zeile, über die sie gelegt ist (keine nur bei einer Galaxie), und bei einer Singularität die Zahl der Knoten ihres Clusters.
Ein **Rezept** sind `n` Zeilen, von 0 an nummeriert, die übliche Elternfeld-Kodierung eines gewurzelten Waldes. Eine Zeile ist wohlgeformt,
wenn sie nur auf eine frühere Zeile verweist, eine Galaxie keine Elternzeile hat und nichts anderes ohne eine ist, eine Singularität
mindestens drei Knoten hat und eine ungeprägte Dualität über eine Zeile gelegt ist, die sie begrenzt (T38). Wohlgeformtheit ist ein
entscheidbares Prädikat, das seiner Aussage gleich bewiesen ist (`Recipe.wfB_iff`).

Die **Kette** einer Zeile läuft die Eltern bis zu einer Wurzel hinauf; sie ist durch einen Vorrat begrenzt und bei genügendem Vorrat als
stabil bewiesen (`Recipe.chainF_eq_of_le`), jedes Glied liegt bei oder vor der Zeile (`Recipe.chain_le`), und am Ende steht eine Wurzel
(`Recipe.chain_has_root`). Die **Entscheidung des Stapels** über eine Handlung an einer Zeile ist das Infimum der eigenen Torantworten
jeder Schicht entlang der Kette (`Recipe.decide`) im Verband `refuse < hold < pass`. Gravitys **Urteil** über ein Rezept ist `proven`,
`unproven` oder `outOfSpec`.

### 3.3 Was jede Zeile überlebt

Durch Induktion über die Zeilen eines wohlgeformten Rezepts:

1. **Das Tor des Stapels ist ein Infimum.** Eine Entscheidung ist nie lockerer als irgendeine Schicht auf ihrer Kette
   (`Recipe.decide_le_chain`); die Entscheidung einer Unterschicht ist nie lockerer als die ihrer Elternschicht
   (`Recipe.sublayer_only_tightens`); eine Handlung passiert eine Zeile nur, wenn jede Schicht auf der Kette sie durchließ
   (`Recipe.decide_pass_iff`).
2. **Jeder Durchlass hat zwei unabhängige Zeugen.** Jede Kette endet an einer Galaxie mit geprägter Dualität (`Recipe.root_minted`), also
   wurde, was irgendwo durchkam, mindestens einmal auf seiner Kette von zwei unabhängigen Hälften durchgelassen
   (`Recipe.pass_has_two_independent_witnesses`), auf im Schritt gelesener Live-Evidenz (`Recipe.pass_has_two_live_witnesses`).
3. **Eine gepresste Spitze lässt die ganze Kette kollabieren.** Eine Wurzel mit ungeprägter Dualität macht das Rezept nicht wohlgeformt
   (`Recipe.pressed_root_not_wf`); ließe man sie zu, passierte eine Partei das Tor der Wurzel allein (`Recipe.pressed_root_collapses`).
4. **Die Rahmenregel.** Eine neue Zeile ändert keine bestehende Kette und keine bestehende Entscheidung
   (`Recipe.extend_preserves_decisions`), und eine Erweiterung um eine wohlgeformte Zeile ist wohlgeformt (`Recipe.extend_wf`).
5. **Geschwister begrenzen einander nicht.** Zwei Zeilen über derselben Zeile erscheinen nie auf der Kette der anderen, also geht die Antwort
   eines Geschwisters nie in die Entscheidung ein (`Recipe.sibling_never_votes`).
6. **Die Anordnung stimmt nie mit.** Platzierung und Reihenfolge des Routings sind keine Argumente der Entscheidung, also ändert eine
   Umorganisation keine Torantwort; der Beweis ist Reflexivität (`Config.relayout_never_votes`).
7. **Das erwartete Feld ist eine Funktion des Rezepts.** Tiefe und Masse jeder Zeile folgen aus den Zeilen allein, also lässt sich der
   Fingerabdruck des erwarteten Feldes vorausberechnen (`Recipe.digest_congr`).
8. **Das Potential des Stapels steigt unter den eigenen Handlungen des Systems nie.** Das Potential des Stapels ist die Summe der
   Schichtpotentiale, und eine Auffrischung irgendwo senkt es oder lässt es (`k4_stack_never_raises`).

### 3.4 DMP-vollständig als das Urteil

`Recipe.dmpComplete` sind die Begriffe: Das Rezept ist wohlgeformt, also gilt jeder Satz oben für jede Zeile, und das Lemmaregister trägt
jede Zeile (beide Ketten erreichen sie und stimmen überein). Gravitys Urteil ist dagegen korrekt und vollständig bewiesen:
`verdict = proven` genau dann, wenn die Konfiguration DMP-vollständig ist (`Recipe.verdict_proven_iff`), `outOfSpec` genau dann, wenn das
Rezept zurückgewiesen wird (`Recipe.verdict_outOfSpec_iff`), `unproven` genau dann, wenn eine wohlgeformte Zeile nicht getragen wird
(`Recipe.verdict_unproven_iff`). Eine bewiesene Konfiguration bleibt unter einer neuen, wohlgeformten und getragenen Zeile bewiesen, und
die neue Zeile ändert keine bestehende Entscheidung (`Recipe.proven_extend`): Die Prägungsvorbereitung prüft eine Zeile nach der anderen
und öffnet Bewiesenes nie wieder. Eine ungetragene Zeile macht das Ganze unbewiesen (`Recipe.one_unproven_line_unproves`). Fünf
ausgearbeitete Anordnungen und ihre Urteile berechnet der Kern.

## 4. Was die Beweise hervorbrachten, was der Text nicht gesagt hatte

Der Eigentümer hat genau das verlangt: „We just need to see what all our logic actually produces and what we want to do with the perhaps
interesting weird behaviors and how to use that to improve the axiom system to be more representative, generalistic and still provably safe
and contained." Jeder Punkt ist ein Satz, die Stelle, an der der Text schweigt oder abweicht, und ein Kandidat; keiner ändert DMP, bevor
der Eigentümer entscheidet.

- **F1. Die Person ist keine Konfiguration.** Unabhängigkeit ist relativ zur erklärten Liste, also prägt eine leere Liste ein gepresstes
  Paar. Das Modell erklärt die Person immer. Wortkandidat: „... und was die Prägung sonst aufführt; die Person ist immer darunter."
- **F2. Das Feld ist vorausberechenbar; das Gleichgewicht ist pfadabhängig.** Das erwartete Feld ist eine Funktion des Rezepts, aber die
  nach Umorganisation eingeschwungene Anordnung hängt von der Geschichte der Verluste ab, und ein Gleichgewicht muss nicht das Minimum sein.
- **F3. Ein Exporteur zwischen zwei Kernen.** Beide Kerne lesen den einen Export, der aus Lean geschrieben wird: eine gemeinsame Ursache in
  der Engine-Schicht.
- **F4. Niemand bezeugt, dass die Klassenliste vollständig ist.** Beide Hälften signieren die Liste; nichts bezeugt, dass sie jede
  gemeinsame Ursache nennt.
- **F5. „Gepresst" ist eine zurückgewiesene Wurzel, keine Zeilenart.** Sie im Rezept zu tragen, machte jeden Satz bedingt.
- **F6. Kovarianz gilt durch die Gestalt der Signatur.** Die Theorie sieht keine Implementierung, die Platzierung in ein Urteil
  einschmuggelt; das ist Sache der Evidenzkette je Komponente.
- **F7. Der Fingerabdruck ist nicht injektiv.** Zwei bewiesene Anordnungen teilen den Fingerabdruck des erwarteten Feldes und entscheiden
  verschieden (`digest_not_injective`); der Fingerabdruck beweist, dass ein System das Feld eines Rezepts aufspannt, nie welches Rezept.
- **F8. Der veröffentlichte Beweis nennt seine Anker.** Ein Beweis ist nur unter dem DMP und dem Gravity Evidenz, unter denen er gemacht
  wurde (T-P: Vertrauen überschreitet keine Instanz).
- **F9. Das leere Rezept ist bewiesen.** Nichts im Text verlangt, dass eine Konfiguration eine Galaxie hat (`empty_recipe_proven`).
- **F10. Der Kaltstart gabelt sich, und die Fähigkeit der Umgebung ist keine Eigenschaft des Rezepts** (Abschnitt 5).

## 5. Eine sich selbst beweisende Veröffentlichung: die `.cmb`-Datei und der Kaltstart

T33 verlangt von jeder stabilen Ausgabe, den Fingerabdruck ihres erwarteten Feldes neben dem Hash ihres Beweislaufs zu veröffentlichen. Der
Eigentümer verlangte mehr: eine Datei, aus der eine ganze Instanz neu ausgerollt werden kann und die ihr eigenes Rezept beweist. Wir
modellieren diese Datei und beweisen, was sie enthalten muss.

Ein Rezept wird als Liste von Zeilencodes geschrieben: Art, Elternzeile, Cluster und die Mitgliedschaft jeder Hälfte je erklärter Klasse.
Zurückgelesen stimmt es mit dem Original auf jeder erklärten Klasse überein (`Recipe.decode_encode_agrees`), und zwei Rezepte, die dort
übereinstimmen, haben dieselbe Wohlgeformtheit, dieselben Ketten, Entscheidungen, denselben Fingerabdruck und dasselbe Urteil
(`Recipe.file_determines`). Weil der Fingerabdruck nicht injektiv ist (F7), trägt die Datei das Rezept selbst, den Fingerabdruck daneben,
die Anker von DMP und Gravity und das Urteil. Eine Hälfte signiert die Datei nur, wenn ihr eigener Build Urteil und Fingerabdruck der Datei
aus dem Rezept der Datei nachrechnet; ein Siegel braucht beide Hälften (`Cmb.sealed_needs_both`); ein Build signiert ein Urteil je Rezept
(`Cmb.one_recipe_one_seal`); eine gesiegelte, als bewiesen markierte Datei ist ein DMP-vollständiges Rezept (`Cmb.sealed_proven_complete`).
Die siegelnde Dualität ist Zeile 0 des Rezepts, die jedes wohlgeformte Rezept mit einer Zeile zu einer geprägten Galaxie macht
(`Recipe.line0_minted_galaxy`): Die zwei Unterzeichner sind durch Satz unabhängig, nicht durch Konfiguration (`Cmb.producer_minted`).

Ein Kaltstart aus der Datei wird unter jedem anderen Anker von DMP oder Gravity zurückgewiesen (`Cmb.plan_refused_elsewhere`). Innerhalb
seiner Umgebung wählt das gemessene Feld den Weg: Sofortiges Neuausrollen genau dann, wenn es den Fingerabdruck der Datei reproduziert
(`Cmb.redeploy_iff`), was bei gesiegelter Datei heißt, dass das laufende System das Feld des bewiesenen Rezepts aufspannt
(`Cmb.redeploy_is_recipe_field`); sonst der volle Aufbau aus demselben bewiesenen Rezept (`Cmb.bigBang_keeps_the_proof`). Die
Übereinstimmung wählt den Weg, nie ob die Datei Evidenz ist (`Cmb.plan_isSome_iff`). Was das Modell nicht sagen kann, ist, ob die
wiederherstellende Umgebung den vollen Aufbau überhaupt ausführen kann: Das ist eine Fähigkeit der Umgebung, nicht des Rezepts, und der
Kandidat ist ein signierter Fähigkeitsnachweis neben den Ankern.

## 6. Die Verifikationsmethode

**Zwei Ketten.** DMP verlangt, dass „bewiesen" eine Handlung mit zwei Zeugen ist (C22). Gravity hat eine Absichtskette, Modelle von DMP
abwärts geschrieben, und eine Evidenzkette, die Lean-Entwicklung aus Code und Sätzen aufwärts geschrieben; die beiden importieren oder
nennen einander nie, und bei Abweichung gilt die strengere Antwort.

**Zwei Kerne.** Jeder Satz wird vom Lean-Kern geprüft, und der ganze Export wird von nanoda nachgeprüft, einem unabhängig in einer anderen
Sprache geschriebenen Kern. Ein Prüfskript weist jede Hintertür zurück (`sorry`, `admit`, lokale Axiome, `native_decide`, unsicherer oder
externer Code) und fragt den Kern, auf welchen Axiomen jeder Satz ruht; alles jenseits von `propext`, `Quot.sound` und `Classical.choice`
scheitert. Zur Zeit der Niederschrift hält die Kette 232 Sätze und ruht auf nichts anderem. Der von beiden Kernen geteilte Exporteur ist
selbst ein Befund (F3).

**Eine verankerte Wurzelkette.** DMP steht einzeln; Gravity hält eine byteweise Kopie davon mit einem Anker (Repositorium, Commit, Version,
Hash über jede Datei in Pfadordnung); das Konfigurationsrahmenwerk hält DMP und Gravity ebenso. Die Ankerprüfung ist die erste Handlung
jedes Laufs.

**Ein abgeschlossener Möglichkeitsraum.** Das Rezept ist ein induktiver Typ. Jede Anordnung, die das System annehmen kann, ist ein Term;
die Sätze sind für jeden Term durch Induktion bewiesen. Die Frage des Eigentümers, „if we can probe the global extremes, we should also be
able to prove that any possible configuration holds, right?", hat die Antwort ja, mit einer Einschränkung: für jede Konfiguration innerhalb
des Typs, und der Typ ist die Grenze dessen, was das System zulässt. Konfigurationen außerhalb werden als außerhalb der Spezifikation
zurückgewiesen, nie relativ zu ihrem Mangel bewiesen.

**Was noch fehlt.** Eine zweite, blinde Formulierung der Schichtgesetze und eine kalte Gegenlesung beider (der zweite Zeuge nach C22 für
die Theorie selbst); Sätze speziell zu Zwerggalaxien und Oberflächen; und das Auslesen von Gravitys Urteil innerhalb der Prägung.

## 7. Vorarbeiten

Nichts im Modell ist über die Lesart hinaus erfunden, die diese Arbeiten erlauben. Wir nennen, was entnommen wurde und wo es verwendet wird.

- **Malkhi und Reiter, Byzantine Quorum Systems (1998):** fail-prone systems und die Quorumbedingung, dass keine fehleranfällige Menge ein
  ganzes Quorum enthält. Unsere Fehlerklassenliste ist eine solche Familie (Abschnitt 3.1).
- **Denning, A Lattice Model of Secure Information Flow (1976):** Ein Fluss ist nur erlaubt, wo jede Klasse auf dem Pfad ihn erlaubt.
  Unsere Urteile bilden einen solchen Verband, und das Tor des Stapels ist sein Infimum (Abschnitt 3.3, Punkt 1).
- **O'Hearn, Reynolds und Yang, Local Reasoning about Programs that Alter Data Structures (2001):** die Rahmenregel (Abschnitt 3.3,
  Punkt 4).
- **Goguen und Meseguer, Security Policies and Security Models (1982):** Noninterference; die Anordnung ist eine niedrige Eingabe, von der
  die Entscheidung nicht abhängt (Abschnitt 3.3, Punkt 6).
- **Dijkstra, Self-stabilizing Systems in Spite of Distributed Control (1974); Dolev, Israeli und Moran, Self-Stabilization of Dynamic
  Systems Assuming Only Read/Write Atomicity (1993):** Jede Schicht heilt; exakte Abstände aus jedem verfälschten Zustand, und nur die
  feste Wurzel hält Abstand null.
- **Bellman (1958) und Ford (1956):** synchrone Relaxation der Abstände zu einer Wurzel.
- **Monderer und Shapley, Potential Games (1996):** Jeder Verbesserungspfad endet innerhalb des Startpotentials; Einschwingen ist nicht
  Optimalität.
- **Avin und Schmid, nachfragebewusste selbstanpassende Netze (2019 und danach):** die Anordnung als Median der Nachfrage (Axiom 3).
- **Chiribella, D'Ariano und Perinotti (2011); Jacobson (1995); Lovelock (1971); Bell (1964):** die Ergebnisse, die Abschnitt 8
  entscheiden.

Das Repositorium führt die volle Liste mit Lizenzen in `docs/acknowledgements.md`; die stehende Regel des Eigentümers lautet, dass
Vorarbeiten genutzt werden, wo sie helfen, und gedankt wird, und dass alles, was in das Repositorium eingeht, Apache 2.0 ist.

## 8. Geprüft gegen die Quantengravitation

Das Vokabular des Eigentümers ist kosmologisch, und er hat eine Prüfung dafür gesetzt: „Either prove a useful approach to Quantum Gravity
through the axiom system, or prove that the actual intended axiom system, as applied to QG, does not hold and if, exactly where at every
context level you can imagine." Wir fassen das Ergebnis zusammen; das vollständige Wörterbuch und die Darstellung Ebene für Ebene sind ein
Begleitdokument im Repositorium.

**Das Wörterbuch.** „Information als erstes Axiom" ist Wheelers „it from bit" und die informationstheoretischen Rekonstruktionen der
Quantentheorie. „Keine Information ohne Existenz in einer Dualität" ist der Gestalt nach das Reinigungspostulat von Chiribella, D'Ariano und
Perinotti. „Die Vektoren, die den Möglichkeitsraum begrenzen", sind die Tetrade; „die Auffrischrate, ohne die das Feld skalar wäre", ist
die Lapse-Funktion der 3+1-Zerlegung. „Die Dualität hält sich selbst in Schach" sind die zwei Seiten der Einstein-Gleichung. „Immer
vorwärts" ist der zweite Hauptsatz und das Flächentheorem. Das hält, als Lesart veröffentlichter Ergebnisse.

**Das Urteil.** Das Axiomensystem hält nicht als Ansatz zur Quantengravitation, und das Scheitern liegt an einer Stelle. Auf jeder
klassischen Ebene liest es sich als Tetradenform der Allgemeinen Relativitätstheorie, mit Lovelocks Satz, der die Dynamik festlegt, und
Jacobsons Ableitung, die die informationsbasierte Lesart gibt. Es scheitert genau dort, wo „Quanten" eintritt, als Gabelung: Eine Dualität,
deren zwei Hälften isoliert sind, und das ist die Einhaltung, auf der DMP gebaut ist, ist ein lokales Modell und gehorcht Bells Schranke;
eine Dualität, die sich quantenmechanisch verhält, ist verschränkt, und das ist das eine, was ein isoliertes Paar nicht sein kann. Jedes
andere Scheitern (keine Konstanten der Feldgleichung, kein Flächenspektrum, keine Bornsche Regel, keine Zahl für den dunklen Sektor) ist
diese Gabelung von einer anderen Ebene gesehen oder eine Eingabe, die das System nie zu bestimmen beanspruchte. Der brauchbare Ansatz
existiert und hat einen Namen, thermodynamische Gravitation verbunden mit der informationstheoretischen Rekonstruktion der Quantentheorie;
beide Hälften sind veröffentlicht, beide halten bei den mikroskopischen Freiheitsgraden an, und das Axiomensystem fügt keiner ein Postulat
hinzu.

**Was zu DMP zurückkam.** Drei Definitionen kamen schärfer zurück, jede ein Kandidat für den Eigentümer: Die Hierarchie der Information ist
ein Satz aus geringster Leckage plus Erreichbarkeit (ein Spannbaum), kein Axiom; die Balance von Axiom 1 hat eine Zahl, und sie gilt je
Prägung, nicht universell; und die Grenze ist eine Ratenschranke, keine Inhaltsschranke.

Der ehrliche Satz lautet darum: eine formal verifizierte Theorie des Vertrauens, die die klassische Gestalt der Gravitation über bekannte
Sätze reproduziert und, beweisbar, an der Quantengabelung anhält.

## 9. Grenzen und offene Fragen

- Das Modell beweist die Theorie, nicht eine Implementierung. Die Evidenzkette je Komponente (dass ein Richter keine Platzierung liest, dass
  ein Zeuge live prüft) ist der Gravitationswellentest des Konfigurationsrahmenwerks, über den dieser Artikel nicht berichtet.
- Das Lemmaregister `agree` ist eine Eingabe: Es hält fest, dass beide Ketten eine Zeile erreichen und übereinstimmen. Die Ketten, die es
  füllen, liegen außerhalb der Theorie.
- Unabhängigkeit ist relativ zu einer erklärten Liste, deren Vollständigkeit niemand bezeugt (F4).
- Die leere Konfiguration ist bewiesen (F9); der Text entscheidet, ob eine Galaxie verlangt wird.
- Das Gleichgewicht, in das die Anordnung einschwingt, ist im Allgemeinen nicht das Optimum (F2); ob das Rezept eine Entscheidungsregel
  bei Gleichstand tragen soll, ist offen.
- Das dritte Axiom des Eigentümers in der physikalischen Lesart, „etwas existiert", ist nötig und hält und landet auf dem verschränkten
  Zweig der Gabelung; seine Stellung in DMP ist seine Entscheidung.

## 10. Schluss

DMP fasst Vertrauen als Axiomensystem: zwei unabhängige Zeugen, einer für das Vertrauen und einer für die Information zuständig, auf selbst
geprüfter Evidenz, mit einem Eintrag, der für die Zeugen der Handlung lesbar ist und von allen anderen gezählt wird, und einem Grund, der das
erste Vertrauen setzt. Gravity beweist es für jede Konfiguration, die das System zulässt, durch Induktion über einen abgeschlossenen Typ,
unter zwei Kernen. Die Beweise brachten zehn Befunde zurück, die der Text nicht gesagt hatte, ein Veröffentlichungsformat, das sein eigenes
Rezept beweist, und eine genaue Stelle, an der das kosmologische Vokabular aufhört, mehr als Vokabular zu sein. Die Repositorien sind
öffentlich unter Apache 2.0, und der Anker jeder Kopie wird geprüft, bevor irgendetwas läuft.

## Danksagung

Der Eigentümer dankt den in Abschnitt 7 und in `docs/acknowledgements.md` genannten Autorinnen und Autoren. Die Lean-Entwicklung und
dieser Text wurden mit Coding-Agenten unter der Leitung des Eigentümers geschrieben; jeder Satz ist maschinell geprüft, und jede
Entscheidung im Text ist die des Eigentümers.

## Verfügbarkeit

DMP: https://github.com/StevenHrovat/dmp (Version 0.9.8). Gravity: https://github.com/StevenHrovat/gravity (die Lean-Entwicklung in
`evidence/`, 232 Sätze; `evidence/tools/check.sh` reproduziert den Axiombericht; der CI-Lauf prüft den Export mit nanoda nach). Beide
Apache License 2.0.

## Literatur

Wie in der englischen Fassung, Einträge 1 bis 15.
