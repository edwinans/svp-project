
# compilation
## 1. Auto-generated Makefile

Only if new files added:  
`coq_makefile -f _CoqProject -o Makefile`

`make`

## 2. Manually
```
coqc -Q . PLF Maps.v
coqc -Q . PLF Imp.v
```

## Open the project file

`emacs Projet.v`
or
`coqide Projet.v`

* Dans les deux cas le contenu de _CoqProject est lu et l'option -Q .
PLF est ajoutée. Si vous utilisez une autre interface, vérifiez
comment faire pour ajouter cette option.
