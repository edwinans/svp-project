
# compilation
## via un makefile autogénéré:

# seulement si un nouveau fichier a été ajouté:
# coq_makefile -f _CoqProject -o Makefile
make

## À la main

coqc -Q . PLF Maps.v
coqc -Q . PLF Imp.v

## Ouvrir le fichier

emacs Projet.v

ou bien:

coqide Projet.v

Dans les deux cas le contenu de _CoqProject est lu et l'option -Q .
PLF est ajoutée. Si vous utilisez une autre interface, vérifiez
comment faire pour ajouter cette option.