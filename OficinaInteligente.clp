;;;; FUNCIONES ÚTILES

;;;(set-fact-duplication TRUE)

;;; Hechos estaticos
(deffacts Habitaciones
	(Habitacion Recepcion)		;;;;  Receptión es una habitación
	(Habitacion Pasillo)
	(Habitacion Oficina1)
	(Habitacion Oficina2)
	(Habitacion Oficina3)
	(Habitacion Oficina4)
	(Habitacion Oficina5)
	(Habitacion OficinaDoble)
	(Habitacion Gerencia)
	(Habitacion Papeleria)
	(Habitacion Aseos)
	(Habitacion AseoHombres)
	(Habitacion AseoMujeres)
)

(deffacts Puertas
	(Puerta Recepcion Pasillo)	;;;; Hay una puerta que comunica Recepción con Pasillo
	(Puerta Pasillo Oficina1)
	(Puerta Pasillo Oficina2)
	(Puerta Pasillo Oficina3)
	(Puerta Pasillo Oficina4)
	(Puerta Pasillo Oficina5)
	(Puerta Pasillo Gerencia)
	(Puerta Pasillo OficinaDoble)
	(Puerta Pasillo Papeleria)
)

(deffacts Empleados
	(Empleado G1 Oficina1 0 0)	;;;;; El empleado G1 atiende en la Oficina 1, lleva 0 tramites y ha empleado 0 segundos
	(Empleado G2 Oficina2 0 0)
	(Empleado G3 Oficina3 0 0)
	(Empleado G4 Oficina4 0 0)
	(Empleado G5 Oficina5 0 0)
	(Empleado E1 OficinaDoble-1 0 0)
	(Empleado E2 OficinaDoble-2 0 0)
	(Empleado Recepcionista Recepcion)
	(Empleado Director Gerencia)
)

(deffacts Codificacion
	(Code TG "Tramites Generales")
	(Code TE "Tramites Especiales")
)

(deffacts Tareas
	(Tarea G1 TG)			;;;;; El empleado G1 atiende Trámites Generales
	(Tarea G2 TG)
	(Tarea G3 TG)
	(Tarea G4 TG)
	(Tarea G5 TG)
	(Tarea E1 TE)			;;;;; El empleado E1 atiende Trámites Especiales
	(Tarea E2 TE)
)

(deffacts Inicializacion
	(Usuarios TG 0)			;;; Inicialmente hay 0 Usuarios de trámites generales
	(UltimoUsuarioAtendido TG 0)	;;; Inicialmente se han atendido 0 usuarios de tramites generales 
	(Usuarios TE 0)			;;; Inicialmente hay 0 Usuarios de trámites especiales
	(UltimoUsuarioAtendido TE 0)	;;; Inicialmente se han atendido 0 usuarios de tramites especiales
	
	;;; Facts para estadisticas
	(TiempoTotalEspera TG 0)
	(TiempoTotalEspera TE 0)
	(PaLaDesviacionEspera TG 0)
	(PaLaDesviacionEspera TE 0)
	
	(TiempoTotalGestion TG 0)
	(TiempoTotalGestion TE 0)
	(PaLaDesviacionGestion TG 0)
	(PaLaDesviacionGestion TE 0)
	
	(Calculados TG 0)	;;; Numero total de ciclos de tramite realizados (espera-gestion-fin)
	(Calculados TE 0)
	
	;(HoraActualizada 0) ;;; Borrar luego
	;(hora_actual 12) ;;; Borrar luego
	
	(Ejecutar)
)
  
(defrule cargarconstantes
	(declare (salience 10000))
	=>
	(load-facts Constantes.txt)
)

(defrule pa_cambiar
	?b <- (cambia ?c)
	?a <- (HoraActualizada ?)
	=>
	(assert (HoraActualizada ?c))
	(retract ?a ?b)
)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;; PASO1 ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;respuestas ante los hechos (Solicitud ?tipotramite) y (Disponible ?empl);;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;; 1A ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
(defrule EncolarUsuario
	?g <- (Solicitud ?tipotramite)
	?f <- (Usuarios ?tipotramite ?n)
	(HoraActualizada ?h)
	=>
	(assert (Usuario ?tipotramite (+ ?n 1))
			(Usuarios ?tipotramite (+ ?n 1))
			(Esperando ?tipotramite (+ ?n 1) ?h) ; Momento en el que el usuario (+ ?n 1) empieza a esperar
	)
	(printout t "Su turno es " ?tipotramite " " (+ ?n 1)  crlf)
	(retract ?f ?g)
)

(defrule Solicitud_Tramite_incorrecta
	; El nombre lo dice todo
	?borrar <-(Solicitud ?S & ~TG & ~TE)
	=>
	(printout t "Lo sentimos, aquí no tramitamos la solicitud " ?S crlf)
	(retract ?borrar)
)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;; 1B ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
(defrule AsignarEmpleado
	?g <- (Disponible ?empl)	;;; Hay un empleado disponible
	(Tarea ?empl ?tipotramite)	;;; Dicho empleado atiende ?tipotramite
	(Empleado ?empl ?ofic ? ?)	;;; El empleado tiene la oficina ?ofic
	
	?f <- (UltimoUsuarioAtendido ?tipotramite ?atendidos)	;;; Comprobamos cual es el siguiente numero para dar
	(Usuarios ?tipotramite ?total)
	(test (< ?atendidos ?total))
	
	(HoraActualizada ?h)
	?info <- (Informacion ?empl ?estado ?descanso)			;;; Para cambiar el estado del empleado
	
	=>
	
	(bind ?a (+ ?atendidos 1))
	
	(assert (Asignado ?empl ?tipotramite ?a))
	(assert (UltimoUsuarioAtendido ?tipotramite ?a))
	(assert (Gestionando ?tipotramite ?a ?h))		;;; Momento en el que empiezan a gestionar al usuario ?a
	
	(retract ?info)
	
	(assert (Informacion ?empl Atendiendo ?descanso))		;;; Cambiamos el empleado a atendiendo
	
	(printout t "Usuario " ?tipotramite ?a ", por favor pase a " ?ofic crlf)
	
	(assert (AniadeAOficina ?ofic))
	
	(retract ?f ?g)
)
  
(defrule RegistrarCaso
	(declare (salience 10))
	(Disponible ?empl)
	?empleado <- (Empleado ?empl ?ofic ?n_realizados ?t_usado)
	?f <- (Asignado ?empl ?tipotramite ?n)
	
	(HoraActualizada ?h)
	(Gestionando ?tipotramite ?n ?t)
	?info <- (Informacion ?empl ?estado ?descanso)
	=>
	(bind ?tiempo (- ?h ?t))
	
	(assert (Empleado ?empl ?ofic (+ ?n_realizados 1) (+ ?t_usado ?tiempo)))	;;; Para realizar las estadisticas de los empleados
	(assert (Tramitado ?empl ?tipotramite ?n))
	(assert (Terminado ?tipotramite ?n ?h))				;;; Momento en el que se termina de realizar el tramite
	
	(retract ?info)
	
	(assert (Informacion ?empl Disponible ?descanso))	;;; Cambiamos el empleado a disponible
	
	(printout t "Fin tramitación del usuario "?tipotramite ?n". "crlf)
	
	(assert (CalculaTiempo ?tipotramite ?n))
	
	(assert (QuitaDeOficina ?ofic))
	
	(retract ?f ?empleado)
)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;; 1C ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  

(defrule EstaCerrado
	; El nombre lo dice todo again
	(declare (salience 10000)) ; Debe de tener mayor prioridad a todas las reglas
	?borrar <- (Solicitud ?)
	(ComienzoAtencion ?ha)
	(FinalJornada ?hc)
	(hora_actual ?hora)
	(or
		(test (< ?hora ?ha))
		(test (>= ?hora ?hc))
	)
	=>
	(printout t crlf "*CERRADO*" crlf "Horario: " ?ha ":00 - "?hc":00" crlf crlf)
	(retract ?borrar)
)
  
(defrule NoposibleEncolarUsuario
	(declare (salience 20))
	?g <- (Solicitud ?tipotramite)
	(Usuarios ?tipotramite ?n)
	(UltimoUsuarioAtendido ?tipotramite ?atendidos)
	(TiempoMedioGestion ?tipotramite ?m)
	(FinalJornada ?h)
	(test (> (* (- ?n ?atendidos) ?m) (mrest ?h)))
	(Code  ?tipotramite ?texto)
	=>
	(printout t "Lo siento pero por hoy no podremos atender mas " ?texto crlf)
	(bind ?a (- ?n ?atendidos))
	(printout t "Hay ya  " ?a " personas esperando y se cierra a las " ?h "h. No nos dara tiempo a atenderle." crlf)
	(retract ?g)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;; 2  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deffacts ContadorEmpleados
	(nEmpleados TG 0)
	(nEmpleados TE 0)
)

(defrule MinimoEmpleados
	(nEmpleados ?tipo ?n & ~0)
	(MinimoEmpleadosActivos ?tipo ?min)
	(test (< ?n ?min)) 
	=>
	(printout t "Ahora mismo hay menos de " ?min " empleados (en concreto " ?n ") antendiendo " ?tipo crlf)
)

(defrule CeroEmpleados
	(nEmpleados ?tipo ?n)
	(test (= ?n 0)) 
	=>
	(printout t "Hay 0 empleados antendiendo " ?tipo crlf)
)

(defrule DemasiadaEspera
	(declare (salience 10000))
	(Esperando ?tipo ?n & ~0 ?t)
	(MaximoEsperaParaSerAtendido ?tipo ?m)
	(HoraActualizada ?h)
	(test (> ?h (+ ?t (* ?m 60))))
	(not (exists (MuchaEspera ?tipo ?n))) ; Para que solo salte una vez
	(not (exists (Gestionando ?tipo ?n ?))) ; El hecho esperando esta guardado aunque se este gestionando
	=>
	(bind ?cuanto (- ?h ?t))
	(assert (MuchaEspera ?tipo ?n))
	(printout t "El usuario numero " ?n " de " ?tipo " esta esperando demasiado." crlf)
)


(defrule DemasiadaGestion
	(declare (salience 10000))
	(Gestionando ?tipo ?n & ~0 ?t)
	(MaximoTiempoGestion ?tipo ?m)
	(HoraActualizada ?h)
	(test (> ?h (+ ?t (* ?m 60))))
	(not (exists (MuchaGestion ?tipo ?n))) ; Para que solo salte una vez
	=>
	(bind ?cuanto (- ?h ?t))
	(assert (MuchaGestion ?tipo ?n))
	(printout t "El usuario numero " ?n " de " ?tipo " lleva mucho tiempo de gestion." crlf)
)


(defrule CalculaTiempos
	(declare (salience 10000))
	?borrar <- (CalculaTiempo ?tipo ?n)
	?borrar1 <- (Calculados ?tipo ?cuantos)
	?esperando <- (Esperando ?tipo ?n ?hespera)
	?gestionando <- (Gestionando ?tipo ?n ?hgestion)
	?terminado <- (Terminado ?tipo ?n ?hfin)
	?f <- (TiempoTotalEspera ?tipo ?cuanto1)
	?g <- (TiempoTotalGestion ?tipo ?cuanto2)
	?f1 <- (PaLaDesviacionEspera ?tipo ?cuanto11)
	?g1 <- (PaLaDesviacionGestion ?tipo ?cuanto22)
	=>
	(bind ?tiempoespera (- ?hgestion ?hespera))
	(bind ?tiempogestion (- ?hfin ?hgestion))
	
	(retract ?f ?g ?f1 ?g1)
	
	(assert (TiempoTotalEspera ?tipo (+ ?cuanto1 ?tiempoespera)))
	(assert (TiempoTotalGestion ?tipo (+ ?cuanto2 ?tiempogestion)))
	(assert (PaLaDesviacionEspera ?tipo (+ ?cuanto11 (* ?tiempoespera ?tiempoespera))))
	(assert (PaLaDesviacionGestion ?tipo (+ ?cuanto22 (* ?tiempogestion ?tiempogestion))))
	
	(assert (Calculados ?tipo (+ ?cuantos 1)))
	
	;(printout t "TIEMPOS ACTUALIZADOS" crlf)
	
	(retract ?borrar ?borrar1 ?esperando ?gestionando ?terminado)
)

(defrule CalculaEstadistica
	(declare (salience 100))
	?f <- (Estadistica ?tipo)
	(Calculados ?tipo ?n)
	
	(TiempoTotalEspera ?tipo ?tesp)
	(TiempoTotalGestion ?tipo ?tgest)
	
	(PaLaDesviacionEspera ?tipo ?tdesvesp)
	(PaLaDesviacionGestion ?tipo ?tdesvgest)
	=>
	; Calculamos la media
	(bind ?media_espera (/ ?tesp ?n))
	(bind ?media_gestion (/ ?tgest ?n))
	
	; Calculamos la varianza
	(bind ?media_espera_2 (* ?media_espera ?media_espera))
	(bind ?media_gestion_2 (* ?media_gestion ?media_gestion))
	
	(bind ?varianza_espera (- (/ ?tdesvesp ?n) ?media_espera_2))
	(bind ?varianza_gestion (- (/ ?tdesvgest ?n) ?media_gestion_2))
	
	; Calculamos la desviacion
	(bind ?desviacion_espera (sqrt ?varianza_espera))
	(bind ?desviacion_gestion (sqrt ?varianza_gestion))
	
	; Pasamos todo a minutos
	(bind ?media_espera (/ ?media_espera 60))
	(bind ?media_gestion (/ ?media_gestion 60))
	(bind ?desviacion_espera (/ ?desviacion_espera 60))
	(bind ?desviacion_gestion (/ ?desviacion_gestion 60))
	
	;(open "ESTADISTICAS.txt" estad "w")	
	(printout estad crlf "TRÁMITES "?tipo" REALIZADOS : " ?n crlf)
	(printout estad "Tiempos (en minutos): " crlf)
	(printout estad "Tiempo medio de espera para " ?tipo" : " ?media_espera crlf)
	(printout estad "Tiempo medio de gestión para " ?tipo " : " ?media_gestion crlf)
	(printout estad "Desviación del tiempo de espera para " ?tipo " : " ?desviacion_espera crlf)
	(printout estad "Desviación del tiempo de gestion para " ?tipo " : " ?desviacion_gestion crlf crlf)
	;(close estad)
	(retract ?f)
	
	;(assert (MediaEspera ?tipo ?media_espera))
	;(assert (MediaGestion ?tipo ?media_gestion))
	;(assert (DesviacionEspera ?tipo ?desviacion_espera))
	;(assert (DesviacionGestion ?tipo ?desviacion_gestion))
)


(defrule NoPuedeEstadistica
	(declare (salience 110))
	?f <- (Estadistica ?tipo)
	(Calculados ?tipo 0)
	=>
	(printout estad crlf "TRÁMITES "?tipo" REALIZADOS : 0 " crlf)
	(printout estad "Ha habido 0 trámites " ?tipo ", por lo que no se pueden calcular estadísticas." crlf crlf)
	(retract ?f)
	;(assert (MediaEspera ?tipo -1))
	;(assert (MediaGestion ?tipo -1))
	;(assert (DesviacionEspera ?tipo -1))
	;(assert (DesviacionGestion ?tipo -1))
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;; 3  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deffacts InformacionEmpleados
	; Informacion.
	; ID empleado.
	; Situacion: 1) Ausente, 2) Atendiendo, 3) Disponible, 4) Descansando
	; Tiempo de descanso
	(Informacion G1 Ausente 0)
	(Informacion G2 Ausente 0)
	(Informacion G3 Ausente 0)
	(Informacion G4 Ausente 0)
	(Informacion G5 Ausente 0)
	(Informacion E1 Ausente 0)
	(Informacion E2 Ausente 0)
	(Informacion Director Ausente 0)
)

(defrule SituacionEmpleado
	?f <- (Situacion ?idempleado)
	(Informacion ?idempleado ?situacion ?descanso)
	=>
	(printout t "El empleado " ?idempleado " se encuentra: " ?situacion crlf)
	(retract ?f)
)

(defrule FichaEmpleado
	?f <- (Ficha ?emp)
	?g <- (Informacion ?emp ?situacion ?descanso)
	(Tarea ?emp ?tipo)
	?fg <- (nEmpleados ?tipo ?n)
	
	(Empleado ?emp ?ofic ? ?)
	
	(HoraActualizada ?h)
	(TiempoMaximoRetraso ?hmax)
	(TiempoMaximoDescanso ?descansomax)
	(ComienzoJornada ?comienzo)
	=>
	; Primero pasamos todo a minutos
	(bind ?hmin (/ ?h 60))
	(bind ?comienzo (* ?comienzo 60))
	(bind ?descanso (/ ?descanso 60))
	
	
	(if (= (str-compare ?situacion "Ausente") 0) then
		(printout t "Llega el empleado " ?emp crlf)
		
		; Si el empleado tarda mas de 15 minutos en llegar
		(if (> ?hmin (+ ?comienzo ?hmax)) then
			(printout t "El empleado " ?emp " ha llegado " (- ?hmin (+ ?comienzo ?hmax))" minutos tarde." crlf)		
		)
		
		(retract ?g ?fg)
		
		(assert (nEmpleados ?tipo (+ ?n 1)))
		(assert (Informacion ?emp Disponible ?descanso))
		;(assert (Disponible ?emp))
		
		;(printout t crlf "ANIADE A OFICINA " ?ofic crlf)
		(assert (AniadeAOficina ?ofic))
	)
	
	
	(if (= (str-compare ?situacion "Atendiendo") 0) then
		(printout t "Se va el empleado " ?emp " mientras estaba atendiendo." crlf)
		
		(retract ?g ?fg)
		
		(assert (nEmpleados ?tipo (- ?n 1)))
		(assert (Informacion ?emp Descansando ?h))
		
		;(assert (QuitaDosDeOficina ?ofic))
		(assert (QuitaDeOficina ?ofic))
	)
	
	
	(if (= (str-compare ?situacion "Disponible") 0) then
		(printout t "Se va el empleado " ?emp crlf)
		
		(retract ?g ?fg)
		
		(assert (nEmpleados ?tipo (- ?n 1)))
		(assert (Informacion ?emp Descansando ?h))
		
		(assert (QuitaDeOficina ?ofic))
	)
	
	
	(if (= (str-compare ?situacion "Descansando") 0) then
		(printout t "Vuelve el empleado " ?emp crlf)
		
		; Si el empleado descansa más de 30 minutos
		(if (>= (- ?hmin ?descanso) ?descansomax) then
			(printout t "El empleado " ?emp " ha descansado demasiado ("(- ?hmin ?descanso)")." crlf)		
		)
		
		(retract ?g ?fg)
		
		(assert (nEmpleados ?tipo (+ ?n 1)))
		(assert (Informacion ?emp Disponible 0))
		;(assert (Disponible ?emp))
		
		(assert (AniadeAOficina ?ofic))
	)
	
	(retract ?f)
)

(defrule FichaDirector
	?f <- (Ficha ?emp & Director)
	?g <- (Informacion ?emp & Director ?situacion ?descanso)
	(Empleado Director ?lugar)
	(HoraActualizada ?h)
	(TiempoMaximoRetraso ?hmax)
	(TiempoMaximoDescanso ?descansomax)
	(ComienzoJornada ?comienzo)
	=>
	; Primero pasamos todo a minutos
	(bind ?hmin (/ ?h 60))
	(bind ?comienzo (* ?comienzo 60))
	(bind ?descanso (/ ?descanso 60))
	
	(if (= (str-compare ?situacion "Ausente") 0) then
		(printout t "Llega el director." crlf)
		
		(if (> ?hmin (+ ?comienzo ?hmax)) then
			(printout t "El director ha llegado " (- ?hmin (+ ?comienzo ?hmax))" minutos tarde." crlf)		
		)
		(retract ?g)
		(assert (Informacion ?emp Disponible ?descanso))
		(assert (AniadeAOficina ?lugar))
	)
		
	(if (= (str-compare ?situacion "Disponible") 0) then
		(printout t "Se va el director." crlf)
		
		(retract ?g)
		(assert (Informacion ?emp Descansando ?h))
		(assert (QuitaDeOficina ?lugar))
	)
	
	
	(if (= (str-compare ?situacion "Descansando") 0) then
		(printout t "Vuelve el director." crlf)
		
		(if (>= (- ?hmin ?descanso) ?descansomax) then
			(printout t "El director ha descansado demasiado ("(- ?hmin ?descanso)")." crlf)		
		)
		
		(retract ?g)
		(assert (Informacion ?emp Disponible 0))
		(assert (AniadeAOficina ?lugar))
	)
	
	(retract ?f)
)





(defrule becareful
	; Una regla para evitar que el empleado no este disponible y haya un fact (Disponible ?emp)
	(declare (salience 10000))
	(Informacion ?emp ?situacion & ~Disponible & ~Atendiendo ?)
	?f <- (Disponible ?emp)
	=>
	(retract ?f)
)

(defrule EmpleadoPocoTrabajador
	(Empleado ?emp ? ?n ?)
	(Tarea ?emp ?tipo)
	(MinimoTramitesPorDia ?tipo ?cuantos)
	(test (< ?n ?cuantos))
	=>
	(printout t "El empleado " ?emp " ha gestionado menos del número ​mínimo de trámites (" ?n " de " ?cuantos ")." crlf) 
)

(defrule EstadisticasEmpleados
	(declare (salience 100))
	?f <- (Estadistica Empleados ?emp)
	(Empleado ?emp ? ?n & ~0 ?tiempo)
	=>
	(bind ?tiempo (/ ?tiempo 60)) ; Pasamos a minutos
	(printout estad crlf "Empleado " ?emp " : "crlf)
	(printout estad "Trámites gestionados : " ?n crlf)
	(printout estad "Tiempo medio de gestión : " (/ ?tiempo ?n) crlf)
	(printout estad "Tiempo total de gestión : " ?tiempo crlf crlf)
	(retract ?f)
)

(defrule EstadisticasEmpleadosCero
	(declare (salience 100))
	?f <- (Estadistica Empleados ?emp)
	(Empleado ?emp ? 0 ?)
	=>
	(printout estad crlf "Empleado " ?emp " : "crlf)
	(printout estad "Trámites gestionados : 0 " crlf crlf)
	(retract ?f)
)


;;;;;;;;;;;;;; REGLA PARA GENERAR LAS ESTADISTICAS AL FINAL DE LA JORNADA ;;;;;;;;;;;;;;

(defrule SeAcaboLoQueSeDaba
	(declare (salience 10000))
	(FinalJornada ?final)
	(hora_actual ?actual)
	(test (>= ?actual ?final))
	(not (exists (ESTADISTICAS YA CALCULADAS)))
	;?borrar <-(ESTADISTICAS)
	=>
	(printout t crlf crlf "Se acabó la jornada." crlf crlf)
	(open "ESTADISTICAS.txt" estad "w")
	(assert (Estadistica TG))
	(assert (Estadistica TE))
	(assert (Estadistica Empleados G1))
	(assert (Estadistica Empleados G2))
	(assert (Estadistica Empleados G3))
	(assert (Estadistica Empleados G4))
	(assert (Estadistica Empleados G5))
	(assert (Estadistica Empleados E1))
	(assert (Estadistica Empleados E2))
	(assert (CIERRAFICHERO))
	(assert (ESTADISTICAS YA CALCULADAS))
	;(retract ?borrar)
)

(defrule Yasta
	?borrar <- (CIERRAFICHERO)
	=>
	(printout t crlf crlf "Estadísticas añadidas al fichero ESTADISTICAS.txt" crlf crlf)
	(close estad)
	(retract ?borrar)
)

;(defrule PrintSensor
;	(Sensor_puerta ?hab)
;	=>
;	(printout t ">>> SE HA ACTIVADO EL SENSOR DE PUERTA " ?hab crlf)
;)

;(defrule PrintFichar
;	(Ficha ?emp)
;	=>
;	(printout t ">>> HA FICHADO EL EMPLEADO " ?emp crlf)
;)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;; 4  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deffacts LucesInicial
	(Luz Recepcion ON)
	(Luz Pasillo OFF)
	(Luz Oficina1 OFF)
	(Luz Oficina2 OFF)
	(Luz Oficina3 OFF)
	(Luz Oficina4 OFF)
	(Luz Oficina5 OFF)
	(Luz OficinaDoble OFF)
	(Luz Gerencia OFF)
	(Luz Papeleria OFF)
	(Luz AseoHombres OFF)
	(Luz AseoMujeres OFF)
)

(defrule EncenderLuzPasillo
	(Sensor_presencia Pasillo)
	?f <- (Luz Pasillo OFF)
	=>
	(printout t "Encender luz pasillo" crlf)
	(assert (Luz Pasillo ON))
	(retract ?f)
)

(defrule ApagarLuzPasillo
	(not (Sensor_presencia Pasillo))
	?f <- (Luz Pasillo ON)
	=>
	(printout t "Apagar luz pasillo" crlf)
	(assert (Luz Pasillo OFF))
	(retract ?f)
)

(defrule AlguienEntra
	(Sensor_puerta ?ofi & ~Pasillo)
	?f <- (Luz ?ofi OFF)
	=>
	;(printout t crlf crlf crlf "ENCIENDE LUZ " ?ofi crlf crlf crlf)
	(assert (Luz ?ofi ON))
	(retract ?f)
)

;(defrule EncenderLuzPresencia
;	(Sensor_presencia ?sitio & Pasillo)
;	?f <- (Luz ?sitio OFF)
;	=>
;	(printout t "Encender luz "?sitio crlf)
;	(assert (Luz ?sitio ON))
;	(assert (entra al ?sitio))
;	(retract ?f)
;)
;
;(defrule ApagarLuzPresencia
;	(not (Sensor_presencia ?sitio & Pasillo))
;	?f <- (Luz ?sitio ON)
;	=>
;	(printout t "Apagar luz " ?sitio crlf)
;	(assert (Luz ?sitio OFF))
;	(retract ?f)
;)
;
;
;
;(defrule EncenderLuz
;	(Sensor_puerta ?sitio & ~Recepcion)
;	?f <- (Luz ?sitio OFF)
;	=>
;	(printout t "Encender luz " ?sitio crlf)
;	(assert (Luz ?sitio ON))
;	(retract ?f)
;)
;
;(defrule ApagarLuz
;	(not (Sensor_puerta ?sitio & ~Recepcion))
;	?f <- (Luz ?sitio ON)
;	=>
;	(printout t "Apagar luz " ?sitio crlf)
;	(assert (Luz ?sitio OFF))
;	(retract ?f)
;)




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;; 5  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deffacts PersonasEnHabitacion
	;;; (nPersonas ?lugar ?numerodepersonas ?maximopersonas)
	(nPersonas Oficina1 0 2) 
	(nPersonas Oficina2 0 2)
	(nPersonas Oficina3 0 2)
	(nPersonas Oficina4 0 2)
	(nPersonas Oficina5 0 2)
	(nPersonas OficinaDoble-1 0 2)
	(nPersonas OficinaDoble-2 0 2)
	(nPersonas Gerencia 0 2) ;;; El director y algún trabajador 
	(nPersonas Papeleria 0 7) ;;; En la papelería solo entran los empleados, 7 personas
)

(defrule VaciaSinJustificacion
	(nPersonas ?ofi & ~Gerencia & ~Papeleria ?cuantos ?)
	(test (= ?cuantos 0))	;;; Comprobamos que en la oficina haya cero personas
	
	(Empleado ?emp ?ofi ? ?)
	(Informacion ?emp ?situacion & ~Descansando ?descanso) ;;; Comprobamos que el empleado de esa oficina no esté descansando
	
	(hora_actual ?hora)
	(ComienzoAtencion ?comienzo)
	(test (>= ?hora ?comienzo))  ;;; Comprobamos que ya haya empeazado la jornada de trabajo
	
	(not (exists (CeroSinJustificacion ?ofi)))
	=>		
	(assert (CeroSinJustificacion ?ofi))
	(printout t "La oficina " ?ofi " está vacía sin justificación." crlf)
)

(defrule BorraCero
	(declare (salience 10000))
	(AniadeAOficina ?ofic)
	?borrar <- (CeroSinJustificacion ?ofic)
	=>
	(retract ?borrar)
)

(defrule DemasiadasPersonasEnOficina
	(nPersonas ?ofi ?cuantos ?maximo)
	(test (> ?cuantos ?maximo))	;;; Comprobamos que en la oficina haya mas de un maximo de personas
	=>
	(printout t "Hay más personas de lo normal en la oficina "?ofi"." crfl)
)


(defrule AniadePersonas
	?borrar1 <- (AniadeAOficina ?ofic)
	?borrar2 <- (nPersonas ?ofic ?cuantos ?max)
	=>
	;(printout t crlf crlf "ANIADO COSAS A " ?ofic crlf crlf)
	(bind ?nuevo (+ ?cuantos 1))
	(assert (nPersonas ?ofic ?nuevo ?max))
	(retract ?borrar1 ?borrar2)
)

(defrule QuitaPersonas
	?borrar1 <- (QuitaDeOficina ?ofic)
	?borrar2 <- (nPersonas ?ofic ?cuantos ?max)
	=>
	;(printout t crlf crlf "QUITO COSAS" crlf crlf)
	(bind ?nuevo (- ?cuantos 1))
	(assert (nPersonas ?ofic ?nuevo ?max))
	(retract ?borrar1 ?borrar2)
)
