/*  Title:      Pure/Concurrent/simple_thread.scala
    Author:     Makarius

Simplified thread operations.
*/

package isabelle


import java.lang.Thread

import scala.actors.Actor


object Simple_Thread
{
  /* plain thread */

  def fork(name: String = "", daemon: Boolean = false)(body: => Unit): Thread =
  {
    val thread =
      if (name == null || name == "") new Thread() { override def run = body }
      else new Thread(name) { override def run = body }
    thread.setDaemon(daemon)
    thread.start
    thread
  }


  /* future result via thread */

  def future[A](name: String = "", daemon: Boolean = false)(body: => A): Future[A] =
  {
    val result = Future.promise[A]
    fork(name, daemon) { result.fulfill_result(Exn.capture(body)) }
    result
  }


  /* thread as actor */

  def actor(name: String, daemon: Boolean = false)(body: => Unit): (Thread, Actor) =
  {
    val actor = Future.promise[Actor]
    val thread = fork(name, daemon) { actor.fulfill(Actor.self); body }
    (thread, actor.join)
  }
}

